#[repr(transparent)]
pub struct S<T: ?Sized> {
    pub t: T,
}

// Custom DST with an array slice

pub const X1: &S<[u8]> = &S { t: [42] };

pub fn f1() -> usize {
    X1.t.len()
}

// Custom DST with a string slice

pub const X2: &S<str> = unsafe { std::mem::transmute("hello") };

pub fn f2() -> usize {
    X2.t.len()
}

// Custom DST with a trait object field

pub trait Trait {
    fn method(&self) -> usize;
}

impl Trait for usize {
    fn method(&self) -> usize { *self }
}

pub const X3: &S<dyn Trait> = &S { t: 42usize };

pub fn f3() -> usize {
    X3.t.method()
}

// Custom DST with an array slice that is produced using `transmute` rather
// than an unsizing coercion

#[repr(C)]
pub struct S1<T: ?Sized> {
    pub x: u32,
    pub y: T,
}

#[repr(C)]
pub struct S2 {
    pub x: u32,
    pub y: [u8],
}

pub const Y: S1<[u8; 4]> = S1 { x: 1, y: [2; 4] };
pub const R1: &S1<[u8]> = &Y;
pub const R2: &S2 = unsafe { std::mem::transmute(R1) };

pub fn r1() -> usize {
    R1.y.len()
}

pub fn r2() -> usize {
    R2.y.len()
}
