pub struct S1<const N: u8>;
pub struct S2<const N: usize>;

pub fn f1<const N: u8>(_: S1<N>) {}
pub fn f2<const N: usize>(_: S2<N>) {}

pub fn g1(s: S1<42u8>) { f1(s) }
pub fn g2(s: S2<42usize>) { f2(s) }
