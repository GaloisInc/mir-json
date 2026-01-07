use core::array;
use core::num::{NonZero, Saturating, Wrapping, ZeroablePrimitive};
use crate::crucible_assume_unreachable;


pub trait Symbolic: Sized {
    /// Create a new symbolic value of this type.  `desc` is used to refer to this symbolic value
    /// when printing counterexamples.
    fn symbolic(desc: &str) -> Self;

    /// Create a new symbolic value, subject to constraints.  The result is a symbolic value of
    /// this type on which `f` returns `true`.
    fn symbolic_where<F: FnOnce(&Self) -> bool>(desc: &str, f: F) -> Self {
        let x = Self::symbolic(desc);
        super::crucible_assume!(f(&x));
        x
    }
}


macro_rules! core_impls {
    ($($ty:ty, $func:ident;)*) => {
        $(
            /// Hook for a crucible override that creates a symbolic instance of $ty.
            #[allow(unused)]
            fn $func(desc: &str) -> $ty { unimplemented!(stringify!($func)); }

            impl Symbolic for $ty {
                fn symbolic(desc: &str) -> $ty { $func(desc) }
            }
        )*
    };
}

core_impls! {
    bool, symbolic_bool;
    u8, symbolic_u8;
    u16, symbolic_u16;
    u32, symbolic_u32;
    u64, symbolic_u64;
    u128, symbolic_u128;
}


macro_rules! usize_impls {
    ($($ty:ty, $width:expr;)*) => {
        $(
            #[cfg(target_pointer_width = $width)]
            impl Symbolic for usize {
                fn symbolic(desc: &str) -> usize { <$ty>::symbolic(desc) as usize }
            }
        )*
    };
}

usize_impls! {
    u8, "8";
    u16, "16";
    u32, "32";
    u64, "64";
    u128, "128";
}


macro_rules! int_impls {
    ($($ty:ty, $uty:ty;)*) => {
        $(
            impl Symbolic for $ty {
                fn symbolic(desc: &str) -> $ty { <$uty>::symbolic(desc) as $ty }
            }
        )*
    };
}

int_impls! {
    i8, u8;
    i16, u16;
    i32, u32;
    i64, u64;
    i128, u128;
    isize, usize;
}


impl<T: Symbolic, const N: usize> Symbolic for [T; N] {
    fn symbolic(desc: &str) -> [T; N] {
        array::from_fn(|_i| T::symbolic(desc))
    }
}


macro_rules! tuple_impls {
    ($($($name:ident)*;)*) => {
        $(
            #[allow(unused)] #[allow(bad_style)]
            impl<$($name: Symbolic,)*> Symbolic for ($($name,)*) {
                fn symbolic(desc: &str) -> ($($name,)*) {
                    (
                        $($name::symbolic(desc),)*
                    )
                }
            }
        )*
    };
}

tuple_impls! {
    ;
    A;
    A B;
    A B C;
    A B C D;
    A B C D E;
    A B C D E F;
    A B C D E F G;
    A B C D E F G H;
    A B C D E F G H I;
    A B C D E F G H I J;
    A B C D E F G H I J K;
    A B C D E F G H I J K L;
}

impl<T: Symbolic> Symbolic for Saturating<T> {
    fn symbolic(desc: &str) -> Saturating<T> {
        Saturating(T::symbolic(desc))
    }
}

impl<T: Symbolic> Symbolic for Wrapping<T> {
    fn symbolic(desc: &str) -> Wrapping<T> {
        Wrapping(T::symbolic(desc))
    }
}

impl<T: Symbolic + ZeroablePrimitive> Symbolic for NonZero<T> {
    fn symbolic(desc: &str) -> NonZero<T> {
        match NonZero::new(T::symbolic(desc)) {
            Some(x) => x,
            None => crucible_assume_unreachable!(),
        }
    }
}

/// Take a symbolic-length prefix of `xs`.  The length of the returned slice can be anywhere in the
/// range `0 ..= xs.len()`.
pub fn prefix<'a, T>(xs: &'a [T]) -> &'a [T] {
    let len = usize::symbolic_where("prefix_len", |&n| n < xs.len());
    &xs[..len]
}
