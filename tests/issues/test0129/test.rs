// test.rs
const X: &[u64] = &[42];
pub static Y: &[&[u64]] = &[&X];

pub fn f() -> &'static [&'static [u64]] {
    &Y
}
