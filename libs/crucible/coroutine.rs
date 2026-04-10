use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

/// Accesses a closure argument of an async future at a specific index.
///
/// # Type Parameters
///
/// * `T` - The coroutine/future type
/// * `U` - The type of the closure argument at index `I`. This must **exactly match**
///   the type of the argument at that index, or symbolic execution will fail with an
///   assertion failure.
/// * `I` - The zero-based index of the closure argument to access. This must be a
///   compile-time constant (statically known), as dynamic runtime indexes are not supported.
pub fn coroutine_field<T, U, const I: usize>(coroutine: *const T) -> *const U {
    unimplemented!("coroutine_field requires crux-mir override")
}

/// Accesses a closure argument of an async future at a specific index, returning an immutable reference.
///
/// # Type Parameters
///
/// * `T` - The coroutine/future type
/// * `U` - The type of the closure argument at index `I`. This must **exactly match**
///   the type of the argument at that index.
/// * `I` - The zero-based index of the closure argument to access (must be statically known).
pub fn coroutine_field_ref<T, U, const I: usize>(coroutine: &T) -> &U {
    unsafe { &*coroutine_field::<T, U, I>(coroutine) }
}

/// Accesses a closure argument of an async future at a specific index, returning a mutable reference.
///
/// # Type Parameters
///
/// * `T` - The coroutine/future type
/// * `U` - The type of the closure argument at index `I`. This must **exactly match**
///   the type of the argument at that index.
/// * `I` - The zero-based index of the closure argument to access (must be statically known).
pub fn coroutine_field_mut<T, U, const I: usize>(coroutine: &mut T) -> &mut U {
    unsafe { &mut *coroutine_field::<T, U, I>(coroutine).cast_mut() }
}

#[macro_export]
#[doc(hidden)]
macro_rules! set_async_override_let_bind {
    ($futref:expr, $i:expr, ) => {};
    ($futref:expr, $i:expr, $maybe_ref:ident $($upvar:ident)? : $UpvarTy:ty, $($rest:tt)*) => {
        let $maybe_ref $($upvar)? : $UpvarTy = *$crate::coroutine::coroutine_field_ref::<_, _, {$i}>($futref);
        $crate::set_async_override_let_bind!($futref, $i+1, $($rest)*);
    };
}

/// Overrides the behavior of an async function during symbolic execution.
///
/// This macro allows you to replace the implementation of an async function with a custom
/// one that can access the function's arguments (captured variables) and return a symbolic
/// or modified result. This is particularly useful for symbolic execution where you want to
/// replace concrete async operations with symbolic ones.
///
/// # Syntax
///
/// ```ignore
/// set_async_override!(
///     target_function,
///     |[ref] arg1: Type1, [ref] arg2: Type2, ...| -> ReturnType {
///         // Implementation body that returns ReturnType
///     }
/// );
/// ```
///
/// ## Key Points
///
/// - **Target expression**: Use the actual function name.
///
/// - **Argument patterns**: Each argument needs its identifier and type. Prefix with `ref` if you want
///   the argument passed by reference (e.g., `ref hi: u32` gives you `&u32` instead of `u32`).
///
/// - **Return type**: Optional. Specify with `-> Type` or omit for `()` (unit type).
///
/// - **Body**: Must return the specified return type (or `()` if omitted).
///
/// # Examples
///
/// ## Basic usage - replace an async function with a symbolic implementation
///
/// ```ignore
/// use crucible::*;
/// use core::task::Poll;
///
/// async fn get_random(lo: u32, hi: u32) -> u32 {
///     // Original implementation would do something async
///     unimplemented!()
/// }
///
/// fn override_get_random() {
///     set_async_override!(
///         get_random,
///         |lo: u32, hi: u32| -> u32 {
///             // Access to actual argument values via upvars
///             Symbolic::symbolic_where("random", |&x| lo <= x && x < hi)
///         }
///     );
/// }
/// ```
///
/// ## Using `ref` for by-reference access
///
/// ```ignore
/// async fn process_data(id: u32, config: Config) -> Result {
///     unimplemented!()
/// }
///
/// fn override_process_data() {
///     set_async_override!(
///         process_data,
///         |id: u32, ref config: Config| -> Result {
///             // `id` is u32, `config` is &Config
///             if config.enabled {
///                 Ok(id)
///             } else {
///                 Err(Error::Disabled)
///             }
///         }
///     );
/// }
/// ```
///
/// # How It Works
///
/// The macro creates a new module scope containing:
/// 1. A type alias for the target future using `impl Future`
/// 2. An alternative implementation function that extracts upvars and runs your custom logic
/// 3. An override installation that replaces the future's `poll` method
#[macro_export]
#[allow_internal_unstable(type_alias_impl_trait)]
macro_rules! set_async_override {

    // Pattern with explicit return type: |[ref] arg1: Type1, ...| -> RetType { body }
    // The pattern `$maybe_ref:ident $($upvar:ident)?` handles both:
    //   - Non-ref: `lo: u32` matches as `$maybe_ref=lo`, no `$upvar`
    //   - Ref: `ref lo: u32` matches as `$maybe_ref=ref`, `$upvar=lo`
    ($target:expr, | $($maybe_ref:ident $($upvar:ident)?: $UpvarTy:ty),* $(,)? | -> $retTy:ty $body:block ) => {{

        // Module needed to help define_opaque resolve its target
        mod __mod {
            // Needed for $retTy and $target
            use super::*;

            // Compiler is too smart to just use panic!() to make the arguments
            fn __undef<T>(_label: &str) -> T { unimplemented!() }

            pub type __TargetFuture = impl core::future::Future<Output = $retTy>;

            #[define_opaque(__TargetFuture)]
            fn __define_target_future() -> __TargetFuture {
                $target( $(__undef(stringify!($UpvarTy))),* )
            }
        }

        fn __alternative_implementation(
            _fut: core::pin::Pin<&mut __mod::__TargetFuture>,
            _cx: &mut core::task::Context,
        ) -> core::task::Poll<<__mod::__TargetFuture as core::future::Future>::Output> {
            $crate::set_async_override_let_bind!(&*_fut, 0, $($maybe_ref $($upvar)? : $UpvarTy,)*);
            core::task::Poll::Ready($body)
        }

        $crate::override_(<__mod::__TargetFuture as core::future::Future>::poll, __alternative_implementation);
    }};

    // Pattern without return type - defaults to (): |[ref] arg1: Type1, ...| { body }
    // This also handles zero arguments: || { body }
    ($target:expr, | $($maybe_ref:ident $($upvar:ident)?: $UpvarTy:ty),* $(,)? | $body:block ) => {{
        $crate::set_async_override!($target, | $($maybe_ref $($upvar)?: $UpvarTy),* | -> () $body)
    }};
}

/// Trivial async executor for use during symbolic execution.
/// All poll operations must immediately succeed when using this.
pub fn trivial_block_on<F: Future>(mut fut: F) -> F::Output {
    let mut cx = Context::from_waker(Waker::noop());
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(x) => x,
        Poll::Pending => panic!("unexpected Pending"),
    }
}
