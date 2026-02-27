use std::mem::transmute;

#[repr(transparent)]
pub struct S1<T: ?Sized> {
    pub t: T,
}

pub struct S2<T: ?Sized, A> {
    pub a: A,
    pub t: T,
}

// Custom DSTs around array slices

pub const X_ARRAY_SLICE_1: &S1<[u8]> = &S1 {
    t: [42],
};

pub fn ex_array_slice_1() -> usize {
    X_ARRAY_SLICE_1.t.len()
}

pub const X_ARRAY_SLICE_2: &S2<[u8], usize> = &S2 {
    a: 27,
    t: [42]
};

pub fn ex_array_slice_2() -> usize {
    X_ARRAY_SLICE_2.a + X_ARRAY_SLICE_2.t.len()
}

// Custom DSTs around string slices

pub const X_STRING_SLICE: &S1<str> = unsafe { transmute ("hello") };

pub fn ex_string_slice() -> usize {
    X_STRING_SLICE.t.len()
}

// Custom DSTs around trait objects

pub trait Trait {
    fn method(&self) -> usize;
}

impl Trait for usize {
    fn method(&self) -> usize { *self }
}

pub const X_TRAIT_OBJECT_1: &S1<dyn Trait> = &S1 {
    t: 42usize,
};

pub fn ex_trait_object_1() -> usize {
    X_TRAIT_OBJECT_1.t.method()
}

pub const X_TRAIT_OBJECT_2: &S2<dyn Trait, usize> = &S2 {
    a: 27usize,
    t: 42usize,
};

pub fn ex_trait_object_2() -> usize {
    X_TRAIT_OBJECT_2.a + X_TRAIT_OBJECT_2.t.method()
}
