#![feature(rustc_private)]
#[macro_use]
extern crate serde_json;

extern crate rustc;
extern crate rustc_driver;
extern crate rustc_mir;
extern crate rustc_const_math;
extern crate rustc_serialize;
extern crate rustc_data_structures;
extern crate getopts;
extern crate syntax;
extern crate rustc_errors;

mod analyz;
use rustc::session::Session;
use rustc_driver::{Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_driver::driver::{CompileState, CompileController};
use rustc::session::config::{self, Input, ErrorOutputType};
use syntax::ast;
use std::path::PathBuf;

struct MyCompilerCalls(RustcDefaultCalls);
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
        matches: &getopts::Matches,
        sess: &Session,
        input: &Input,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
    ) -> Compilation {
        self.0.late_callback(matches, sess, input, odir, ofile)
    }
    fn build_controller(
        &mut self,
        sess: &Session,
        matches: &getopts::Matches,
    ) -> CompileController<'a> {
        let mut control = self.0.build_controller(sess, matches);
        control.after_analysis.callback = Box::new(after_analysis);
        control
    }
}

fn after_analysis<'a, 'tcx>(state: &mut CompileState<'a, 'tcx>) {
    state.session.abort_if_errors();

    analyz::analyze(state);
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
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => {
            option_env!("RUST_SYSROOT")
                .expect(
                    "need to specify RUST_SYSROOT env var or use rustup or multirust",
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
    args.push("-Zno-trans".to_owned());

    rustc_driver::run_compiler(
        &args, // args: &[String]
        &mut MyCompilerCalls(RustcDefaultCalls), // callbacks: &mut CompilerCalls
        None, // file_loader: Option<stuff>
        None,
    ); // emitter_dest: Option<stuff>
    // -> (CompileResult, Option<Session>)

}

fn main() {
    go();
}
