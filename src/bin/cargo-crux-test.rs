//! `cargo crux-test`: Run symbolic tests of the current crate.
//!
//! Symbolic tests are identified by the `#[crux_test]` attribute, analogous to the `#[test]`
//! attribute used with `cargo test`.  Symbolic tests often need to use the `crucible` crate, which
//! is unavailable when building normally, and thus should be conditionally compiled using
//! `#[cfg(crux)]`.
//!
//! Crux-specific build options can be set in the `[package.metadata.crux]` section of
//! `Cargo.toml`.  Currently supported options:
//!
//!  * `use_override_crates` (list of strings): Use Crux overrides for the named crates.  These
//!    crates will be hidden from their downstream dependencies, causing fallback to the
//!    verifier-friendly implementations shipped with Crux.

#![feature(rustc_private)]
extern crate cargo;
extern crate clap;
extern crate rustc;
extern crate rustc_session;
extern crate serde_json;

use std::env;
use std::path::PathBuf;
use std::process::{self, Command};
use rustc_session::config::host_triple;
use cargo::util::command_prelude::*;

fn cli() -> App {
    // Copy-pasted from cargo/src/bin/cargo/commands/test.rs, with minor edits to the text.
    subcommand("crux-test")
        .setting(AppSettings::TrailingVarArg)
        .about("Execute all symbolic unit tests of a local package")
        .arg(
            Arg::with_name("TESTNAME")
                .help("If specified, only run tests containing this string in their names"),
        )
        .arg(
            Arg::with_name("args")
                .help("Arguments for the test binary")
                .multiple(true)
                .last(true),
        )
        .arg(
            opt(
                "quiet",
                "Display one character per test instead of one line",
            )
            .short("q"),
        )
        .arg_targets_all(
            "Test only this package's library unit tests",
            "Test only the specified binary",
            "Test all binaries",
            "Test only the specified example",
            "Test all examples",
            "Test only the specified test target",
            "Test all tests",
            "Test only the specified bench target",
            "Test all benches",
            "Test all targets",
        )
        .arg(opt("doc", "Test only this library's documentation"))
        .arg(opt("no-run", "Compile, but don't run tests"))
        .arg(opt("no-fail-fast", "Run all tests regardless of failure"))
        .arg_package_spec(
            "Package to run tests for",
            "Test all packages in the workspace",
            "Exclude packages from the test",
        )
        .arg_jobs()
        .arg_release("Build artifacts in release mode, with optimizations")
        .arg_profile("Build artifacts with the specified profile")
        .arg_features()
        .arg_target_triple("Build for the target triple")
        .arg_target_dir()
        .arg_manifest_path()
        .arg_message_format()
        .after_help("See `cargo test --help` for more information on these options.")
}

/// Get the list of crates for which crux-mir overrides should be used.
fn get_override_crates() -> String {
    // `cargo metadata` output includes the settings for each crate in the build, but gives us no
    // way to determine which crates we're actually building, as that's controlled by various
    // options that are specific to `cargo test`.  So instead we use the `cargo` library, including
    // a copy of `cargo test`'s command-line argument definitions (which are not exported), to
    // parse the arguments just like `cargo test` does and figure out which packages it intends to
    // test.
    let config = cargo::Config::default()
        .unwrap_or_else(|e| panic!("error initializing cargo config: {}", e));
    let app = clap::App::new("cargo-crux-test").subcommand(cli());
    let args = app.get_matches();
    let args = args.subcommand_matches("crux-test")
        .unwrap_or_else(|| panic!("expected crux-test subcommand"));
    let ws = args.workspace(&config)
        .unwrap_or_else(|e| panic!("error building workspace: {}", e));
    let opts = args.compile_options(
        &config,
        CompileMode::Test,
        Some(&ws),
        ProfileChecking::Unchecked,
    ).unwrap_or_else(|e| panic!("error reading compile options: {}", e));
    let pkgs = opts.spec.get_packages(&ws)
        .unwrap_or_else(|e| panic!("error listing packages: {}", e));

    if pkgs.len() == 0 {
        return "".to_owned();
    }

    // If this build contains multiple packages, they all must agree on the set of overrides to
    // use.  This is because the override settings affect the builds of the dependencies, which are
    // shared by all packages in the workspace.
    let overrides = get_package_override_crates(pkgs[0].manifest().custom_metadata());
    for pkg in pkgs.iter().skip(1) {
        let pkg_overrides = get_package_override_crates(pkg.manifest().custom_metadata());
        if pkg_overrides != overrides {
            panic!(
                "can't compile multiple packages with different crux overrides\n\
                - package {} overrides {:?}\n\
                - package {} overrides {:?}\n\
                try testing only a single package instead",
                pkgs[0].package_id(),
                overrides,
                pkg.package_id(),
                pkg_overrides,
            );
        }
    }

    overrides
}

fn get_package_override_crates(v: Option<&toml::Value>) -> String {
    get_package_override_crates_opt(v)
        .unwrap_or_else(String::new)
}

fn get_package_override_crates_opt(v: Option<&toml::Value>) -> Option<String> {
    // The `crux` key is allowed to be missing, but if present, it must be an object.
    let crux = v?.get("crux")?;
    assert!(crux.is_table(), "expected `package.metadata.crux` to be an object");
    let overrides = crux.get("use_override_crates")?;
    assert!(overrides.is_array(), "expected `crux.use_override_crates` to be an array");
    let mut overrides = overrides.as_array().unwrap().iter().map(|x| {
        assert!(x.is_str(), "expected `crux.use_override_crates` items to be strings");
        x.as_str().unwrap().to_owned()
    }).collect::<Vec<_>>();
    overrides.sort();
    Some(overrides.join(" "))
}

fn main() {
    let cargo = env::var("CARGO").unwrap();

    // First arg is this binary's name, second arg is the cargo argument `crux-test` that caused
    // this binary to be invoked.
    let orig_args = env::args().skip(2).collect::<Vec<_>>();

    let mut args = Vec::new();
    args.push("test".into());
    // XXX big hack.  See `mir-json-rustc-wrapper.rs` for an explanation of why we set `--target`
    // explicitly to its default value.
    args.push("--target".into());
    args.push(host_triple().into());
    args.extend(orig_args.into_iter());

    let my_path = PathBuf::from(env::args_os().nth(0).unwrap());
    let wrapper_path = if let Some(dir) = my_path.parent() {
        dir.join("mir-json-rustc-wrapper")
    } else {
        PathBuf::from("mir-json-rustc-wrapper")
    };

    let override_crates = get_override_crates();

    let status = Command::new(&cargo)
        .args(&args)
        .env("RUSTC_WRAPPER", wrapper_path)
        .env("CRUX_USE_OVERRIDE_CRATES", override_crates)
        .status().unwrap();
    // `code` can return `None` if the process was terminated by a signal.  We return nonzero
    // ourselves in that case.
    process::exit(status.code().unwrap_or(1));
}

