pub fn dup<C: Clone>(x: C) -> (C, C) {
    (x.clone(), x)
}

pub fn f(x: i32) -> i32 {
    x
}

pub fn g() -> i32 {
    (dup(f).0)(42)
}
