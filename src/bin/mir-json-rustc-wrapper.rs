//! Entry point for use with `cargo crux-test` / `RUSTC_WRAPPER`.  This will export MIR (like the
//! main `mir-json` binary), and if this is a top-level build, it will also link in all libraries
//! as specified by `--extern` and/or `#![no_std]` and run `mir-verifier` on the result.
#![feature(rustc_private)]

extern crate rustc_codegen_ssa;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate getopts;
extern crate rustc_ast;
extern crate rustc_errors;
extern crate rustc_target;
extern crate rustc_session;

extern crate mir_json;

use mir_json::analyz;
use mir_json::link;
use rustc_session::config::Externs;
use rustc_driver::Compilation;
use rustc_interface::interface::{Compiler, Config};
use rustc_interface::Queries;
use rustc_session::config::ExternLocation;
use std::collections::HashSet;
use std::env;
use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::iter;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;


/// Driver callbacks that get the output filename and then stop compilation.  This is used to get
/// the path of the test executable when compiling in `--test` mode.
#[derive(Default)]
struct GetOutputPathCallbacks {
    output_path: Option<PathBuf>,
    use_override_crates: HashSet<String>,
}

impl rustc_driver::Callbacks for GetOutputPathCallbacks {
    fn config(&mut self, config: &mut Config) {
        scrub_externs(&mut config.opts.externs, &self.use_override_crates);
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // This phase runs with `--cfg crux`, so some `#[crux_test]` attrs may be visible.  Even
        // the limited amount of compilation we do will fail without the injected `register_attr`.
        analyz::inject_attrs(queries);
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let sess = compiler.session();
        let crate_name = queries.crate_name().unwrap().peek();
        let outputs = queries.prepare_outputs().unwrap().peek();
        self.output_path = Some(rustc_session::output::out_filename(
            sess,
            sess.crate_types().first().unwrap().clone(),
            &outputs,
            &crate_name,
        ));
        Compilation::Stop
    }
}

fn get_output_path(args: &[String], use_override_crates: &HashSet<String>) -> PathBuf {
    let mut callbacks = GetOutputPathCallbacks {
        output_path: None,
        use_override_crates: use_override_crates.clone(),
    };
    rustc_driver::RunCompiler::new(&args, &mut callbacks).run().unwrap();
    callbacks.output_path.unwrap()
}

fn scrub_externs(externs: &mut Externs, use_override_crates: &HashSet<String>) {
    let new_externs = Externs::new(externs.iter().map(|(k, v)| {
        let k = k.clone();
        let mut v = v.clone();
        if use_override_crates.contains(&k) {
            v.location = ExternLocation::FoundInLibrarySearchDirectories;
        }
        (k, v)
    }).collect());
    *externs = new_externs;
}


#[derive(Debug, Default)]
struct MirJsonCallbacks {
    analysis_data: Option<analyz::AnalysisData<()>>,
    use_override_crates: HashSet<String>,
}

impl rustc_driver::Callbacks for MirJsonCallbacks {
    fn config(&mut self, config: &mut Config) {
        scrub_externs(&mut config.opts.externs, &self.use_override_crates);
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::inject_attrs(queries);
        Compilation::Continue
    }

    fn after_expansion<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        analyz::gather_match_spans(queries);
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        self.analysis_data = analyz::analyze(compiler.session(), queries).unwrap();
        Compilation::Continue
    }
}

fn link_mirs(main_path: PathBuf, extern_paths: &[PathBuf], out_path: &Path) {
    let mut inputs = iter::once(&main_path).chain(extern_paths.iter())
        .map(File::open)
        .collect::<io::Result<Vec<_>>>().unwrap();
    let output = io::BufWriter::new(File::create(out_path).unwrap());
    link::link_crates(&mut inputs, output).unwrap();
}

fn write_test_script(script_path: &Path, json_path: &Path) -> io::Result<()> {
    let json_name = json_path.file_name().unwrap().to_str().unwrap();
    let mut f = OpenOptions::new().write(true).create(true).truncate(true)
        .mode(0o755).open(script_path)?;
    writeln!(f, "#!/bin/sh")?;
    writeln!(f, r#"exec "${{CRUX_MIR:-crux-mir}}" --assert-false-on-error --cargo-test-file "$(dirname "$0")"/'{}' "$@""#, json_name)?;
    Ok(())
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

    let mut use_override_crates = HashSet::new();
    if let Ok(s) = env::var("CRUX_USE_OVERRIDE_CRATES") {
        for name in s.split(" ") {
            use_override_crates.insert(name.to_owned());
        }
    }


    let test_idx = match args.iter().position(|s| s == "--test") {
        None => {
            eprintln!("normal build - {:?}", args);
            // This is a normal, non-test build.  Just run the build, generating a `.mir` file
            // alongside the normal output.
            rustc_driver::RunCompiler::new(
                &args,
                &mut MirJsonCallbacks {
                    analysis_data: None,
                    use_override_crates: use_override_crates.clone(),
                },
            ).run().unwrap();
            return;
        },
        Some(x) => x,
    };

    // This is a `--test` build.  We need to build the `.mir`s for this crate, link with `.mir`s
    // for all its dependencies, and produce a test script (in place of the test binary expected by
    // cargo) that will run `crux-mir` on the linked JSON file.

    // We're still using the original args (with only a few modifications), so the output path
    // should be the path of the test binary.
    eprintln!("test build - extract output path - {:?}", args);
    let test_path = get_output_path(&args, &use_override_crates);

    args.remove(test_idx);

    args.push("--cfg".into());
    args.push("crux_top_level".into());

    // Cargo doesn't pass a crate type for `--test` builds.  We fill in a reasonable default.
    args.push("--crate-type".into());
    args.push("rlib".into());

    eprintln!("test build - {:?}", args);

    // Now run the compiler.  Note we rely on cargo providing different metadata and extra-filename
    // strings to prevent collisions between this build's `.mir` output and other builds of the
    // same crate.
    let mut callbacks = MirJsonCallbacks {
        analysis_data: None,
        use_override_crates: use_override_crates.clone(),
    };
    rustc_driver::RunCompiler::new(&args, &mut callbacks).run().unwrap();
    let data = callbacks.analysis_data
        .expect("failed to find main MIR path");

    let json_path = test_path.with_extension(".linked-mir.json");
    eprintln!("linking {} mir files into {}", 1 + data.extern_mir_paths.len(), json_path.display());
    eprintln!(
        "  inputs: {}{}",
        data.mir_path.display(),
        data.extern_mir_paths.iter().map(|x| format!(" {}", x.display())).collect::<String>(),
    );
    link_mirs(data.mir_path, &data.extern_mir_paths, &json_path);

    write_test_script(&test_path, &json_path).unwrap();
    eprintln!("generated test script {}", test_path.display());
}

fn main() {
    go();
}
