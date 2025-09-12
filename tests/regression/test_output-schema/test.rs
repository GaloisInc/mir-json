pub trait T {
    fn foo(&self) -> i32;
}

pub struct S;

impl T for S {
    fn foo(&self) -> i32 { 42 }
}

pub fn call_foo(x: &dyn T) -> i32 {
    x.foo()
}
