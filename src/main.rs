#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_codegen_utils;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate getopts;
extern crate syntax;
extern crate rustc_errors;

extern crate mir_json;

use mir_json::analyz;
use rustc::session::Session;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc::session::config::{self, Input, ErrorOutputType};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_metadata::cstore::CStore;
use syntax::ast;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

struct MirJsonCallbacks;

impl rustc_driver::Callbacks for MirJsonCallbacks {
    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis(&mut self, compiler: &Compiler) -> Compilation {
        analyz::analyze(compiler).unwrap();
        Compilation::Continue
    }
}

const TARGET_FILE: &'static str = "crucible-unknown-none.json";

const TARGET_JSON: &'static str = r#"
    {
      "llvm-target": "x86_64-unknown-linux-gnu",
      "target-endian": "little",
      "target-pointer-width": "64",
      "target-c-int-width": "32",
      "os": "none",
      "env": "none",
      "vendor": "unknown",
      "arch": "crucible",
      "data-layout": "e-m:e-i64:64-f80:128-n8:16:32:64-S128",
      "linker-flavor": "gcc"
    }
"#;

fn go() {
    let mut args: Vec<String> = std::env::args().collect();

    let target_flag = String::from("--target");
    if !args.contains(&target_flag) {
        if !Path::new(TARGET_FILE).exists() {
            let mut f = File::create(&TARGET_FILE).unwrap();
            f.write_all(TARGET_JSON.as_bytes()).unwrap();
        }

        args.push(target_flag);
        args.push(TARGET_FILE.into());
    }

    rustc_driver::run_compiler(
        &args, // args: &[String]
        &mut MirJsonCallbacks,
        None,
        None,
    ).unwrap();
}

fn main() {
    go();
}
