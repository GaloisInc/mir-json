//! Common functionality shared between `cargo-crux-test` and `cargo-saw-build`.

use std::env;
use std::path::PathBuf;
use std::process::{self, Command};
use rustc_session::config::host_tuple;
use cargo::util::command_prelude::{*, Command as CargoCommand};
use toml::Value as TomlValue;

fn cli(subcmd_name: &'static str, subcmd_descr: &'static str) -> CargoCommand {
    // Copy-pasted from
    // https://github.com/rust-lang/cargo/blob/d73d2caf9e41a39daf2a8d6ce60ec80bf354d2a7/src/bin/cargo/commands/test.rs,
    // with minor edits to the text.
    subcommand(subcmd_name)
        // Subcommand aliases are handled in `aliased_command()`.
        // .alias("t")
        .about(subcmd_descr)
        .arg(
            Arg::new("TESTNAME")
                .action(ArgAction::Set)
                .help("If specified, only run tests containing this string in their names"),
        )
        .arg(
            Arg::new("args")
                .value_name("ARGS")
                .help("Arguments for the test binary")
                .num_args(0..)
                .last(true),
        )
        .arg(flag("no-run", "Compile, but don't run tests"))
        .arg(flag("no-fail-fast", "Run all tests regardless of failure"))
        .arg_future_incompat_report()
        .arg_message_format()
        .arg(
            flag(
                "quiet",
                "Display one character per test instead of one line",
            )
            .short('q'),
        )
        .arg_package_spec(
            "Package to run tests for",
            "Test all packages in the workspace",
            "Exclude packages from the test",
        )
        .arg_targets_all(
            "Test only this package's library",
            "Test only the specified binary",
            "Test all binaries",
            "Test only the specified example",
            "Test all examples",
            "Test only the specified test target",
            "Test all targets that have `test = true` set",
            "Test only the specified bench target",
            "Test all targets that have `bench = true` set",
            "Test all targets (does not include doctests)",
        )
        .arg(
            flag("doc", "Test only this library's documentation")
                .help_heading(heading::TARGET_SELECTION),
        )
        .arg_features()
        .arg_jobs()
        .arg_unsupported_keep_going()
        .arg_release("Build artifacts in release mode, with optimizations")
        .arg_profile("Build artifacts with the specified profile")
        .arg_target_triple("Build for the target triple")
        .arg_target_dir()
        .arg_unit_graph()
        .arg_timings()
        .arg_manifest_path()
        .arg_lockfile_path()
        .arg_ignore_rust_version()
        .after_help(
            "Run `<cyan,bold>cargo help test</>` for more detailed information.\n\
             Run `<cyan,bold>cargo test -- --help</>` for test binary options.\n",
        )
}

/// Get the list of crates for which crux-mir overrides should be used.
fn get_override_crates(subcmd_name: &'static str, subcmd_descr: &'static str) -> String {
    // `cargo metadata` output includes the settings for each crate in the build, but gives us no
    // way to determine which crates we're actually building, as that's controlled by various
    // options that are specific to `cargo test`.  So instead we use the `cargo` library, including
    // a copy of `cargo test`'s command-line argument definitions (which are not exported), to
    // parse the arguments just like `cargo test` does and figure out which packages it intends to
    // test.
    let gctx = cargo::GlobalContext::default()
        .unwrap_or_else(|e| panic!("error initializing cargo global context: {}", e));
    let program_name = format!("cargo-{}", subcmd_name);
    let cmd = CargoCommand::new("cargo")
        .bin_name(program_name.clone())
        .display_name(program_name)
        .subcommand(cli(subcmd_name, subcmd_descr));
    let args = cmd.get_matches();
    let args = args.subcommand_matches(subcmd_name)
        .unwrap_or_else(|| panic!("expected {} subcommand", subcmd_name));
    let ws = args.workspace(&gctx)
        .unwrap_or_else(|e| panic!("error building workspace: {}", e));
    let opts = args.compile_options(
        &gctx,
        UserIntent::Test,
        Some(&ws),
        ProfileChecking::Custom,
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

fn get_package_override_crates(v: Option<&TomlValue>) -> String {
    get_package_override_crates_opt(v)
        .unwrap_or_else(String::new)
}

fn get_package_override_crates_opt(v: Option<&TomlValue>) -> Option<String> {
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

pub fn cargo_test_common(subcmd_name: &'static str, subcmd_descr: &'static str,
                         extra_args: &Vec<String>, extra_env_vars: &Vec<(String, String)>) {
    let cargo = env::var("CARGO").unwrap();

    // First arg is this binary's name, second arg is the cargo argument
    // `crux-test`/`saw-build` that caused this binary to be invoked.
    let orig_args = env::args().skip(2).collect::<Vec<_>>();

    let mut args = Vec::new();
    args.push("test".into());
    // XXX big hack.  See `mir-json-rustc-wrapper.rs` for an explanation of why we set `--target`
    // explicitly to its default value.
    if !orig_args.iter().any(|a| a == "--target") {
        args.push("--target".into());
        args.push(host_tuple().into());
    }
    let mut export_all = false;
    if orig_args.iter().any(|a| a == "--branch-coverage") {
        export_all = true;
    }
    for extra_arg in extra_args {
        args.push(extra_arg.into());
    }
    args.extend(orig_args.into_iter());

    let my_path = PathBuf::from(env::args_os().nth(0).unwrap());
    let wrapper_path = if let Some(dir) = my_path.parent() {
        dir.join("mir-json-rustc-wrapper")
    } else {
        PathBuf::from("mir-json-rustc-wrapper")
    };

    let override_crates = get_override_crates(subcmd_name, subcmd_descr);

    let mut cmd = Command::new(&cargo);
    cmd.args(&args)
       .env("RUSTC_WRAPPER", wrapper_path)
       .env("CRUX_USE_OVERRIDE_CRATES", override_crates);
    if export_all { cmd.env("EXPORT_ALL","true"); }
    for (extra_env_var_name, extra_env_var_val) in extra_env_vars {
        cmd.env(extra_env_var_name, extra_env_var_val);
    }
    let status = cmd.status().unwrap();
    // `code` can return `None` if the process was terminated by a signal.  We return nonzero
    // ourselves in that case.
    process::exit(status.code().unwrap_or(1));
}
