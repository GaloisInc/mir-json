#![feature(rustc_private)]

extern crate serde;
#[macro_use]
extern crate serde_json;

extern crate rustc;
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate syntax;

pub mod analyz;
