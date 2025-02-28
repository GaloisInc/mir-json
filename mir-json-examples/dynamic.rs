#![feature(optin_builtin_traits)]

use std::any::Any;
fn f(x: &dyn Iterator<Item=u32>) {}
fn g(f: &dyn Fn(bool) -> char) {}
fn h(x: &(dyn Any + Sync + Send)) {}
fn i(f: &(dyn Fn(bool) -> char + Send)) {}
fn j(s: &dyn Send) {}

// Does not compile on our current version of `rustc`
//fn switch(s: &(dyn Send + Sync)) -> &(dyn Sync + Send) { s }

auto trait Foo {}
fn testauto(s: &(dyn Send + Foo)) {}
