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
