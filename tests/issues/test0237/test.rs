pub trait Trait {
    fn method(&self) -> u32;
}

impl Trait for u32 {
    fn method(&self) -> u32 { *self }
}

const X: &dyn Trait = &0u32;

pub fn f() -> u32 {
    X.method()
}
