//! Entry point for use with `cargo crux-test` / `RUSTC_WRAPPER`.  This will export MIR (like the
//! main `mir-json` binary), and if this is a top-level build, it will also link in all libraries
//! as specified by `--extern` and/or `#![no_std]` and run `mir-verifier` on the result.
#![feature(rustc_private)]

extern crate rustc;
extern crate rustc_codegen_utils;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate getopts;
extern crate syntax;
extern crate rustc_errors;
extern crate rustc_target;
extern crate tempfile;

extern crate mir_json;

use mir_json::analyz;
use mir_json::link;
use rustc::session::Session;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{Compiler, Config};
use rustc::session::config::{self, Input, ErrorOutputType};
use rustc_codegen_utils::codegen_backend::CodegenBackend;
use rustc_metadata::cstore::CStore;
use rustc_target::spec::PanicStrategy;
use syntax::ast;
use std::env;
use std::error::Error;
use std::fs::File;
use std::io::{self, Write};
use std::iter;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::NamedTempFile;

#[derive(Debug, Default)]
struct MirJsonCallbacks {
    analysis_data: Option<analyz::AnalysisData>,
}

impl rustc_driver::Callbacks for MirJsonCallbacks {
    fn config(&mut self, config: &mut Config) {
        // Force `-C panic=abort` - the mir-verifier backend doesn't support unwinding.
        config.opts.cg.panic = Some(PanicStrategy::Abort);
    }

    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis(&mut self, compiler: &Compiler) -> Compilation {
        self.analysis_data = analyz::analyze(compiler).unwrap();
        Compilation::Continue
    }
}

fn link_mirs(main_path: PathBuf, extern_paths: &[PathBuf]) -> NamedTempFile {
    let mut temp_file = tempfile::Builder::new().suffix(".mir.json").tempfile().unwrap();

    let mut inputs = iter::once(&main_path).chain(extern_paths.iter())
        .map(File::open)
        .collect::<io::Result<Vec<_>>>().unwrap();
    let mut output = io::BufWriter::new(temp_file.as_file_mut());
    link::link_crates(&mut inputs, output).unwrap();

    ::std::fs::copy(temp_file.path(), "out.json").unwrap();

    temp_file
}

fn go() {
    // First arg is the name of the `rustc` binary that cargo means to invoke, which we ignore.
    let mut args: Vec<String> = std::env::args().skip(1).collect();

    // XXX big hack: We need to use normal rustc (with its normal libs) for `build.rs` scripts,
    // since our custom libs aren't actually functional.  To distinguish `build.rs` and `build.rs`
    // dependencies from other compilation jobs, we pass `--target x86_64-unknown-linux-gnu` to
    // `cargo`.  This makes cargo use cross-compilation mode, even though the host and target
    // triples are the same.  In that mode, it passes the provided `--target` through to target
    // jobs, and omit `--target` for host jobs.  So if `--target` is missing, this is a `build.rs`
    // build, and we should `exec` the real Rust compiler instead of doing our normal thing.
    if args.iter().position(|s| s == "--target").is_none() {
        let rustc = &args[0];
        let args = &args[1..];
        eprintln!("this is a host build - exec {:?} {:?}", rustc, args);
        let e = Command::new(rustc)
            .args(args)
            .exec();
        unreachable!("exec failed: {:?}", e);
    }

    // All build steps need `--cfg crux` and library paths.
    args.push("--cfg".into());
    args.push("crux".into());

    if let Ok(s) = env::var("CRUX_RUST_LIBRARY_PATH") {
        args.push("-L".into());
        args.push(s);
    }

    // The final build step is identified by a special `+mir-json-top-level` argument.  For that
    // build step, we add `--cfg crux_top_level`, which causes all `#[crux_test]` functions to be
    // treated as entry points.  We also do extra work after running the compiler - see below.
    let top_level_marker_idx = args.iter().position(|s| s == "+mir-json-top-level");
    let is_top_level = top_level_marker_idx.is_some();
    if let Some(idx) = top_level_marker_idx {
        args.remove(idx);
        args.push("--cfg".into());
        args.push("crux_top_level".into());
    }

    let mut callbacks = MirJsonCallbacks::default();
    rustc_driver::run_compiler(
        &args,
        &mut callbacks,
        None,
        None,
    ).unwrap();

    if is_top_level {
        let data = callbacks.analysis_data
            .expect("failed to find main MIR path");
        let temp_file = link_mirs(data.mir_path, &data.extern_mir_paths);
        let status = Command::new("crux-mir")
            .arg("-f")
            .arg(temp_file.path())
            .status()
            .unwrap_or_else(|e| panic!("failed to start crux-mir: {}", e));
        assert!(status.success(), "crux-mir failed: exit status {}", status);
    }
}

fn main() {
    go();
}
