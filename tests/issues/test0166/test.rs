#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::future::Future;
use std::ops::Coroutine;
use std::pin::Pin;
use std::task::{Context, Waker};

pub fn f() {
    let mut coroutine = #[coroutine] || {
        yield 1;
        return "foo"
    };

    let p = Pin::new(&mut coroutine);
    p.resume(());
}

pub fn g() {
    async fn bar() -> &'static str {
        return "bar"
    }

    let s = bar();
    let mut p = Box::pin(s);
    let mut context = Context::from_waker(Waker::noop());
    let _ = p.as_mut().poll(&mut context);
}
