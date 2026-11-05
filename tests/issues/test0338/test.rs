// test.rs
#![no_std]

extern crate crucible;
use crucible::*;

cryptol! {
    path "Cryptol";
    pub fn f<const N: u64>() -> u64 = r"{N} : [64]";
}

#[crux::test]
pub fn crux_test() {
    let lhs = f::<42>();
    let rhs = 42;
    crucible_assert!(lhs == rhs, "{:?} != {:?}", lhs, rhs);
}
