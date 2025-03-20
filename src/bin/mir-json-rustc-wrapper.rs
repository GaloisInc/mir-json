//! Entry point for use with `cargo crux-test` / `RUSTC_WRAPPER`.  This will export MIR (like the
//! main `mir-json` binary), and if this is a top-level build, it will also link in all libraries
//! as specified by `--extern` and/or `#![no_std]` and run `crux-mir` on the result.
#![feature(rustc_private)]
#![feature(byte_slice_trim_ascii)]

extern crate rustc_codegen_ssa;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_ast;
extern crate rustc_errors;
extern crate rustc_target;
extern crate rustc_session;

extern crate mir_json;

use mir_json::analyz;
use mir_json::link;
use rustc_session::config::{self, Externs};
use rustc_session::getopts;
use rustc_driver::Compilation;
use rustc_interface::interface::{Compiler, Config};
use rustc_interface::Queries;
use rustc_session::config::ExternLocation;
use std::collections::HashSet;
use std::env;
use std::ffi::OsStr;
use std::fs::{File, OpenOptions, read_dir};
use std::io::{self, Write};
use std::iter;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::prelude::OsStrExt;
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
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // This phase runs with `--cfg crux`, so some `#[crux::test]` attrs may be visible.  Even
        // the limited amount of compilation we do will fail without the injected `register_attr`.
        analyz::inject_attrs(queries);

        let sess = compiler.session();
        let (crate_name, outputs) = {
            // rustc_session::find_crate_name - get the crate with queries.expansion?
            let krate = queries.parse().unwrap();
            let krate = krate.borrow();
            let crate_name = rustc_session::output::find_crate_name(&sess, &krate.attrs);
            let outputs = compiler.build_output_filenames(&sess, &krate.attrs);
            (crate_name, outputs)
        };
        // Advance the state slightly further, initializing crate_types()
        queries.register_plugins();
        self.output_path = Some(rustc_session::output::out_filename(
            sess,
            sess.crate_types().first().unwrap().clone(),
            &outputs,
            crate_name,
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
    export_style: analyz::ExportStyle,
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
        self.analysis_data = analyz::analyze(compiler.session(), queries, self.export_style).unwrap();
        Compilation::Continue
    }
}

fn parse_rustc_args(rustc_args: &[String]) -> getopts::Matches {
    let mut options = getopts::Options::new();
    for option in config::rustc_optgroups() {
        (option.apply)(&mut options);
    }
    options.parse(rustc_args).unwrap()
}

fn exec_host_build(rustc: &str, rustc_args: &[String]) -> ! {
    eprintln!("this is a host build - exec {:?} {:?}", rustc, rustc_args);
    let e = Command::new(rustc)
        .args(rustc_args)
        .exec();
    panic!("exec failed: {:?}", e);
}

fn build_std_crate(
    mut wrapper_args: Vec<String>,
    rustc_opt_matches: &getopts::Matches,
    crate_name: &str,
) {
    let Some(custom_sources_dir) = env::var_os("CRUX_RUST_SOURCES_PATH")
        .or(env::var_os("SAW_RUST_SOURCES_PATH"))
    else {
        if env::var_os("MIR_JSON_USE_RUSTC_SOURCES").is_some() {
            return;
        }
        panic!("TODO error message");
    };
    let custom_sources_dir = Path::new(&custom_sources_dir);
    let orig_rs_path_str = &rustc_opt_matches.free[0];
    let orig_rs_path = Path::new(orig_rs_path_str);
    let orig_crate_dir = env::current_dir()
        .expect("RUSTC_WRAPPER cwd should be accessible");
    let rel_rs_path = orig_rs_path.strip_prefix(orig_crate_dir)
        .expect("rust source file should be inside RUSTC_WRAPPER cwd");
    let mut custom_rs_path = custom_sources_dir.to_path_buf();
    custom_rs_path.push(crate_name);
    custom_rs_path.push(rel_rs_path);
    let rs_path_arg = wrapper_args
        .iter_mut()
        .find(|arg| *arg == orig_rs_path_str)
        .expect("parsed free string should be in arguments");
    *rs_path_arg = custom_rs_path
        .into_os_string()
        .into_string()
        .expect("custom source path should be UTF-8");
    if crate_name == "compiler_builtins" {
        let rustc = wrapper_args[0].clone();
        run_custom_build(wrapper_args);
        let mut crucible_rs_path = custom_sources_dir.to_path_buf();
        crucible_rs_path.push("crucible");
        crucible_rs_path.push("lib.rs");
        let crucible_rs_path = crucible_rs_path
            .into_os_string()
            .into_string()
            .expect("crucible source path should be UTF-8");
        let compiler_builtins_out_dir = rustc_opt_matches
            .opt_str("out-dir")
            .expect("rustc should be passed --out-dir");
        let compiler_builtins_rlib_path = Path::new(&compiler_builtins_out_dir)
            .
        run_wrapper(vec![
            rustc,
            "--crate-name".into(),
            "crucible".into(),
            "--edition".into(),
            "2021".into(),
            crucible_rs_path,
            "--extern".into(),
            // format!("compiler_builtins={}", )
        ])
    } else {
        run_custom_build(wrapper_args);
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

fn run_custom_build(mut driver_args: Vec<String>) {
    // All build steps need `--cfg crux` and library paths.
    driver_args.push("--cfg".into());
    driver_args.push("crux".into());

    let mut use_override_crates = HashSet::new();
    if let Ok(s) = env::var("CRUX_USE_OVERRIDE_CRATES") {
        for name in s.split(" ") {
            use_override_crates.insert(name.to_owned());
        }
    }

    let export_style = if env::var("EXPORT_ALL").is_ok() {
        analyz::ExportStyle::ExportAll
    } else {
        analyz::ExportStyle::ExportCruxTests
    };


    let test_idx = match driver_args.iter().position(|s| s == "--test") {
        None => {
            eprintln!("normal build - {:?}", driver_args);
            // This is a normal, non-test build.  Just run the build, generating a `.mir` file
            // alongside the normal output.
            rustc_driver::RunCompiler::new(
                &driver_args,
                &mut MirJsonCallbacks {
                    analysis_data: None,
                    use_override_crates: use_override_crates.clone(),
                    export_style,
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
    eprintln!("test build - extract output path - {:?}", driver_args);
    let test_path = get_output_path(&driver_args, &use_override_crates);

    driver_args.remove(test_idx);

    driver_args.push("--cfg".into());
    driver_args.push("crux_top_level".into());

    // Cargo doesn't pass a crate type for `--test` builds.  We fill in a reasonable default.
    driver_args.push("--crate-type".into());
    driver_args.push("rlib".into());

    eprintln!("test build - {:?}", driver_args);

    // Now run the compiler.  Note we rely on cargo providing different metadata and extra-filename
    // strings to prevent collisions between this build's `.mir` output and other builds of the
    // same crate.
    let mut callbacks = MirJsonCallbacks {
        analysis_data: None,
        use_override_crates: use_override_crates.clone(),
        export_style,
    };
    rustc_driver::RunCompiler::new(&driver_args, &mut callbacks).run().unwrap();
    let data = callbacks.analysis_data
        .expect("failed to find main MIR path");

    let json_path = test_path.with_extension("linked-mir.json");
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

fn run_wrapper(wrapper_args: Vec<String>) {
    // First argument to this program (second in env::args) is the name of the
    // `rustc` binary that cargo means to invoke.
    // The rest are the arguments that cargo is passing to `rustc`.
    let rustc = &wrapper_args[0];
    let rustc_args = &wrapper_args[1..];

    let rustc_opt_matches = parse_rustc_args(rustc_args);
    let crate_name = rustc_opt_matches.opt_str("crate-name");

    // XXX big hack: We need to use normal rustc (with its normal libs) for `build.rs` scripts,
    // since our custom libs aren't actually functional.  To distinguish `build.rs` and `build.rs`
    // dependencies from other compilation jobs, we pass `--target x86_64-unknown-linux-gnu` to
    // `cargo`.  This makes cargo use cross-compilation mode, even though the host and target
    // triples are the same.  In that mode, it passes the provided `--target` through to target
    // jobs, and omit `--target` for host jobs.  So if `--target` is missing, this is a `build.rs`
    // build, and we should `exec` the real Rust compiler instead of doing our normal thing.
    if !rustc_opt_matches.opt_present("target") {
        exec_host_build(rustc, rustc_args);
    }
    if let Some(crate_name) = crate_name {
        // TODO: talk about `___`
        if crate_name == "___" {
            exec_host_build(rustc, rustc_args);
        }
        if let Ok(std_crates) = env::var("MIR_JSON_STD_CRATES") {
            if std_crates.split_ascii_whitespace().any(|c| c == crate_name) {
                build_std_crate(wrapper_args, &rustc_opt_matches, &crate_name);
                return;
            }
        }
    }

    run_custom_build(wrapper_args);
}

fn main() {
    // First arg is the name of this program, which we ignore.
    run_wrapper(env::args().skip(1).collect());
}
