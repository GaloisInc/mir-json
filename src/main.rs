#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_codegen_utils;
extern crate rustc_driver;
extern crate rustc_metadata;
extern crate getopts;
extern crate syntax;
extern crate rustc_errors;

extern crate mir_json;

use mir_json::analyz;
use rustc::session::Session;
use rustc_driver::{Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_driver::driver::{CompileState, CompileController};
use rustc::session::config::{self, Input, ErrorOutputType};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_metadata::cstore::CStore;
use syntax::ast;
use std::error::Error;
use std::path::PathBuf;

struct MyCompilerCalls(Box<RustcDefaultCalls>);
// below heavily inspired from miri
impl<'a> CompilerCalls<'a> for MyCompilerCalls {
    fn early_callback(
        &mut self,
        matches: &getopts::Matches,
        sopts: &config::Options,
        cfg: &ast::CrateConfig,
        descriptions: &rustc_errors::registry::Registry,
        output: ErrorOutputType,
    ) -> Compilation {
        self.0.early_callback(
            matches,
            sopts,
            cfg,
            descriptions,
            output,
        )
    }
    fn no_input(
        &mut self,
        matches: &getopts::Matches,
        sopts: &config::Options,
        cfg: &ast::CrateConfig,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
        descriptions: &rustc_errors::registry::Registry,
    ) -> Option<(Input, Option<PathBuf>)> {
        self.0.no_input(
            matches,
            sopts,
            cfg,
            odir,
            ofile,
            descriptions,
        )
    }
    fn late_callback(
        &mut self,
        codegen_backend: &dyn CodegenBackend,
        matches: &getopts::Matches,
        sess: &Session,
        cstore: &CStore,
        input: &Input,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
    ) -> Compilation {
        self.0.late_callback(codegen_backend, matches, sess, cstore, input, odir, ofile)
    }
    fn build_controller(
        self: Box<Self>,
        sess: &Session,
        matches: &getopts::Matches,
    ) -> CompileController<'a> {
        let this = *self;
        let mut control = this.0.build_controller(sess, matches);
        control.after_analysis.callback = Box::new(after_analysis);
        control
    }
}

fn after_analysis(state: &mut CompileState) {
    state.session.abort_if_errors();

    analyz::analyze(state).unwrap_or_else(
        |msg| state.session.err(msg.description()));
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

    let result = rustc_driver::run(move || {
        rustc_driver::run_compiler(
            &args, // args: &[String]
            Box::new(MyCompilerCalls(Box::new(RustcDefaultCalls))),
            None,
            None,
        ) // emitter_dest: Option<stuff>
    });    // -> (CompileResult, Option<Session>)
    std::process::exit(result as i32);
}

fn main() {
    go();
}
