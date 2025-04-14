#[macro_use]
pub mod macros;
mod float_traits;
mod hex_float;
mod int_traits;

#[allow(unused_imports)]
pub use float_traits::{Float, IntTy};
pub(crate) use float_traits::{f32_from_bits, f64_from_bits};
#[allow(unused_imports)]
pub use hex_float::{hf32, hf64};
pub use int_traits::{CastFrom, CastInto, DInt, HInt, Int, MinInt};
