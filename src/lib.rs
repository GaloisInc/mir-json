#![feature(rustc_private)]

extern crate serde;
#[macro_use] extern crate serde_json;
extern crate serde_cbor;
#[macro_use] extern crate serde_derive;
extern crate tar;

extern crate rustc;
extern crate rustc_codegen_utils;
extern crate rustc_driver;
extern crate rustc_data_structures;
extern crate rustc_interface;
extern crate rustc_mir;
extern crate rustc_target;
extern crate syntax;

pub mod analyz;
pub mod lib_util;
pub mod link;

mod tar_stream;
