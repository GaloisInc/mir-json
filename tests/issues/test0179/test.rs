pub enum Void {}

pub fn f(v: Void) -> Void {
    v
}

pub fn g(v: Void) -> Void {
    f(v)
}
