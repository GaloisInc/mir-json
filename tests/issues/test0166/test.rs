#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::Coroutine;
use std::pin::Pin;

pub fn main() {
    let mut coroutine = #[coroutine] || {
        yield 1;
        return "foo"
    };

    let p = Pin::new(&mut coroutine);
    p.resume(());
}
