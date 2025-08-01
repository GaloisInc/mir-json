use core::cell::UnsafeCell;

/// Load a Cryptol definition.  `module_path` must be the path to a Cryptol module file, and `name`
/// must be an identifier defined within that module.  The type parameter `F` must be a function
/// pointer type matching the type of the Cryptol definition.  For example, if the Cryptol
/// definition has type `[8] -> [8] -> [8]`, then `F` must be `fn(u8, u8) -> u8`, `fn(i8, i8) ->
/// u8`, or some similar combination.
pub fn load<F>(module_path: &str, name: &str) -> F {
    unimplemented!("cryptol::load")
}

/// Load the Cryptol function `name` from `module_path` and install it as an override for the
/// function `f`.  `f` must be a function definition, not a function pointer or closure, and its
/// signature must match the signature of the Cryptol function.  For example, if the Cryptol
/// definition has type `[8] -> [8] -> [8]`, then `f` must have the signature `fn(u8, u8) -> u8`,
/// `fn(i8, i8) -> u8`, or some similar combination.
pub fn override_<F>(f: F, module_path: &str, name: &str) {
    unimplemented!("cryptol::override")
}

/// Mark the given Cryptol name to be treated as uninterpreted for the duration
/// of the current test.
pub fn uninterp(name: &str) {
    unimplemented!("cryptol::uninterp")
}

#[doc(hidden)]
#[macro_export]
macro_rules! cryptol_function_name {
    ($custom_name:expr, $ident:ident) => { $custom_name };
    ($ident:ident) => { stringify!($ident) };
}

#[macro_export]
macro_rules! cryptol {

    // This pattern does not support const-generics, so its expression is
    // not processed by format!. Therefore its use of curly braces will not
    // need to be escaped.
    (
        path $path:expr;

        $(#[$attr:meta])*
        $pub_:vis fn $name:ident
                ( $($arg_name:ident : $arg_ty:ty),* )
                $( -> $ret_ty:ty )?
                $(= $cryptol_name:expr)? ;
        $($rest:tt)*
    ) => {
        $(#[$attr])*
        #[allow(unconditional_recursion)]
        $pub_ fn $name($($arg_name: $arg_ty),*) $(-> $ret_ty)? {
            // The first call to `$name` loads the Cryptol definition and installs it as an
            // override for `$name` itself.  The recursive call below, and all future calls to
            // `$name`, will dispatch directly to the Cryptol override.
            $crate::cryptol::override_(
                $name,
                $path,
                $crate::cryptol_function_name!($($cryptol_name,)? $name),
            );
            $name($($arg_name),*)
        }
        $crate::cryptol! { path $path; $($rest)* }
    };

    // This pattern supports definitions with const generics. The cryptol
    // expression will be processed by format! which will allow the generic
    // parameters to be accessed by name, e.g. `{N}`. Any regular use of
    // curly braces in the expression will need to be escaped,
    // e.g. `{{` or `}}`.
    (
        path $path:expr;

        $(#[$attr:meta])*
        $pub_:vis fn $name:ident
                < $(const $N:ident: usize),* >
                ( $($arg_name:ident : $arg_ty:ty),* )
                $( -> $ret_ty:ty )?
                = $cryptol_name:expr ;
        $($rest:tt)*
    ) => {
        $(#[$attr])*
        #[allow(unconditional_recursion)]
        $pub_ fn $name< $(const $N: usize),* >($($arg_name: $arg_ty),*) $(-> $ret_ty)? {
            $crate::cryptol::override_(
                $name::< $($N),* >,
                $path,
                &format!($cryptol_name),
            );
            $name::< $($N),* >($($arg_name),*)
        }
        $crate::cryptol! { path $path; $($rest)* }
    };

    (
        path $path:expr;
    ) => {
    };
}

/// Convert all what4 expressions within `x` to saw-core and back.  The resulting expressions will
/// be equivalent but not necessarily identical.
pub fn munge<T>(x: T) -> T {
    x
}
