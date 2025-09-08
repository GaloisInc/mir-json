pub trait A {
    type Output;
    fn a(&self) -> Self::Output;
}

pub trait B: A<Output = i32> {
    fn b(&self) -> i32;
}

pub fn f(x: &dyn B) -> i32 {
    x.a()
}
