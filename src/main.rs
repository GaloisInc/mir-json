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
use std::path::PathBuf;

struct MirJsonCallbacks;

impl rustc_driver::Callbacks for MirJsonCallbacks {
    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis(&mut self, compiler: &Compiler) -> Compilation {
        analyz::analyze(compiler).unwrap();
        Compilation::Continue
    }
}

fn find_sysroot() -> String {
    if let Ok(sysroot) = std::env::var("MIR_JSON_SYSROOT") {
        return sysroot;
    }

    if let Ok(sysroot) = std::env::var("MIRI_SYSROOT") {
        return sysroot;
    }

    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain =
        option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => {
            format!("{}/toolchains/{}", home, toolchain)
        }
        _ => {
            option_env!("RUST_SYSROOT")
                .expect(
                    "need to specify RUST_SYSROOT or use rustup or multirust",
                )
                .to_owned()
        }
    }
}

fn go() {
    let mut args: Vec<String> = std::env::args().collect();

    let sysroot_flag = String::from("--sysroot");
    if !args.contains(&sysroot_flag) {
        args.push(sysroot_flag);
        args.push(find_sysroot());
    }

    args.push("-Zalways-encode-mir".to_owned());
    //args.push("-Zno-trans".to_owned());

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
