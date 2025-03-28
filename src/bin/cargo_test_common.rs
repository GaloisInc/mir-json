//! Common functionality shared between `cargo-crux-test` and `cargo-saw-build`.

use std::env;
use std::path::PathBuf;
use std::process::{self, Command};
use rustc_session::config::host_triple;
use cargo::util::command_prelude::*;
use toml_edit::easy::value::Value as TomlValue;

fn cli(subcmd_name: &'static str, subcmd_descr: &'static str) -> App {
    // Copy-pasted from
    // https://github.com/rust-lang/cargo/blob/ba45764a2c0101a7bac8168f8ea8ba408e9ac6e9/src/bin/cargo/commands/test.rs,
    // with minor edits to the text.
    subcommand(subcmd_name)
        // Subcommand aliases are handled in `aliased_command()`.
        // .alias("t")
        .trailing_var_arg(true)
        .about(subcmd_descr)
        .arg(
            Arg::new("TESTNAME")
                .help("If specified, only run tests containing this string in their names"),
        )
        .arg(
            Arg::new("args")
                .help("Arguments for the test binary")
                .multiple_values(true)
                .last(true),
        )
        .arg(
            opt(
                "quiet",
                "Display one character per test instead of one line",
            )
            .short('q'),
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
        .arg_ignore_rust_version()
        .arg_message_format()
        .arg_unit_graph()
        .arg_future_incompat_report()
        .arg_timings()
        .after_help("See `cargo test --help` for more information on these options.")
}

/// Get the list of crates for which crux-mir overrides should be used.
fn get_override_crates(subcmd_name: &'static str, subcmd_descr: &'static str) -> String {
    // `cargo metadata` output includes the settings for each crate in the build, but gives us no
    // way to determine which crates we're actually building, as that's controlled by various
    // options that are specific to `cargo test`.  So instead we use the `cargo` library, including
    // a copy of `cargo test`'s command-line argument definitions (which are not exported), to
    // parse the arguments just like `cargo test` does and figure out which packages it intends to
    // test.
    let config = cargo::Config::default()
        .unwrap_or_else(|e| panic!("error initializing cargo config: {}", e));
    let app = App::new(format!("cargo-{}", subcmd_name)).subcommand(cli(subcmd_name, subcmd_descr));
    let args = app.get_matches();
    let args = args.subcommand_matches(subcmd_name)
        .unwrap_or_else(|| panic!("expected {} subcommand", subcmd_name));
    let ws = args.workspace(&config)
        .unwrap_or_else(|e| panic!("error building workspace: {}", e));
    let opts = args.compile_options(
        &config,
        CompileMode::Test,
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
        args.push(host_triple().into());
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
    for (extra_env_var_name, extra_env_var_val) in extra_env_vars {
        cmd.env(extra_env_var_name, extra_env_var_val);
    }
    let status = cmd.status().unwrap();
    // `code` can return `None` if the process was terminated by a signal.  We return nonzero
    // ourselves in that case.
    process::exit(status.code().unwrap_or(1));
}
