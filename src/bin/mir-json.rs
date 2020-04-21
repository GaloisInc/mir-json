#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_codegen_ssa;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_session;
extern crate getopts;
extern crate rustc_errors;
extern crate rustc_target;
extern crate rustc_ast;

extern crate mir_json;

use mir_json::analyz;
use rustc_session::Session;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};
use rustc_interface::Queries;
use rustc_session::config::{self, Input, ErrorOutputType};
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_metadata::creader::CStore;
use rustc_target::spec::PanicStrategy;
use rustc_ast::ast;
use std::error::Error;
use std::fs::File;
use std::io::Write;
use std::path::Path;

struct MirJsonCallbacks;

impl rustc_driver::Callbacks for MirJsonCallbacks {
    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::inject_attrs(queries);
        Compilation::Continue
    }

    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::analyze(compiler.session(), queries).unwrap();
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
      "arch": "x86_64",
      "data-layout": "e-m:e-i64:64-f80:128-n8:16:32:64-S128",
      "linker-flavor": "gcc"
    }
"#;

fn go() {
    let mut args: Vec<String> = std::env::args().collect();

    /*
    let target_flag = String::from("--target");
    if !args.contains(&target_flag) {
        if !Path::new(TARGET_FILE).exists() {
            let mut f = File::create(&TARGET_FILE).unwrap();
            f.write_all(TARGET_JSON.as_bytes()).unwrap();
        }

        args.push(target_flag);
        args.push(TARGET_FILE.into());
    }
    */

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
