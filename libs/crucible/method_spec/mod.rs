//! Provides the `MethodSpec` type, used for compositional reasoning.  Also provides
//! `MethodSpecBuilder`, which is used internally by the compositional reasoning macros to
//! construct a `MethodSpec` from a symbolic test.
//!
//! Note that these types work only when running under `crux-mir-comp`.  Trying to use them under
//! ordinary `crux-mir` will produce an error.
use core::fmt;

mod raw;

pub use self::raw::clobber_globals;


/// The specification of a function.  This can be used when verifying callers of the function to
/// avoid simulating the entire function itself.
#[derive(Clone, Copy)]
pub struct MethodSpec {
    raw: raw::MethodSpec,
}

impl MethodSpec {
    /// Enable this `MethodSpec` to be used as an override for its subject function.
    pub fn enable(&self) {
        raw::spec_enable(self.raw);
    }

    pub fn pretty_print(&self) -> &'static str {
        raw::spec_pretty_print(self.raw)
    }
}

impl fmt::Debug for MethodSpec {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let s = raw::spec_pretty_print(self.raw);
        fmt.write_str("MethodSpec {")?;
        for (i, chunk) in s.split("\n").enumerate() {
            if i > 0 {
                fmt.write_str(", ")?;
            }
            fmt.write_str(chunk);
        }
        fmt.write_str("}")?;
        Ok(())
    }
}


/// Helper type used to incrementally construct a `MethodSpec` for a function.
pub struct MethodSpecBuilder {
    raw: raw::MethodSpecBuilder,
}

impl fmt::Debug for MethodSpecBuilder {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "MethodSpecBuilder {{ .. }}")
    }
}

impl MethodSpecBuilder {
    pub fn new<Args: core::marker::Tuple, F: Fn<Args>>(f: F) -> MethodSpecBuilder {
        MethodSpecBuilder {
            raw: raw::builder_new::<F>(),
        }
    }

    pub fn add_arg<T>(&mut self, x: &T) {
        self.raw = raw::builder_add_arg(self.raw, x);
    }

    pub fn gather_assumes(&mut self) {
        self.raw = raw::builder_gather_assumes(self.raw);
    }

    pub fn set_return<T>(&mut self, x: &T) {
        self.raw = raw::builder_set_return(self.raw, x);
    }

    pub fn gather_asserts(&mut self) {
        self.raw = raw::builder_gather_asserts(self.raw);
    }

    pub fn finish(self) -> MethodSpec {
        MethodSpec {
            raw: raw::builder_finish(self.raw),
        }
    }
}
