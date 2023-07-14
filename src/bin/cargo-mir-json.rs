/* Heavily inspired by cargo-miri */
extern crate cargo_metadata;

use std::env;
use std::path::{PathBuf, Path};
use std::process;
use std::io::Write;
use std::process::Command;

const CARGO_MIR_JSON_HELP: &str = r#"Translates crates into MIR encoded in JSON

Usage:
    cargo mir-json [options] [--] [<opts>...]

Common options:
    -h, --help               Print this message
    -V, --version            Print version info and exit

Other options are the same as `cargo rustc`.
"#;

fn show_help() {
    println!("{}", CARGO_MIR_JSON_HELP);
}

fn show_version() {
    println!("{}", env!("CARGO_PKG_VERSION"));
}

fn main() {
    // Check for version and help flags even when invoked as 'cargo-mir-json'
    if env::args().any(|a| a == "--help" || a == "-h") {
        show_help();
        return;
    }
    if env::args().any(|a| a == "--version" || a == "-V") {
        show_version();
        return;
    }

    if let Some("mir-json") = env::args().nth(1).as_ref().map(AsRef::as_ref) {
        // this arm is when `cargo mir-json` is called

        let test = env::args().nth(2).map_or(false, |text| text == "test");
        let skip = if test { 3 } else { 2 };

        let manifest_path_arg = env::args().skip(skip).find(|val| {
            val.starts_with("--manifest-path=")
        });
        let manifest_path = manifest_path_arg.map(|arg| {
            PathBuf::from(Path::new(&arg["--manifest-path=".len()..]))
        });

        let mut metadata_command = cargo_metadata::MetadataCommand::new();
        if let Some(manifest_path) = manifest_path.as_ref() {
            metadata_command.manifest_path(manifest_path);
        }
        let mut metadata = if let Ok(metadata) = metadata_command.exec() {
            metadata
        } else {
            let _ = std::io::stderr().write_fmt(format_args!(
                "error: Could not obtain cargo metadata."
            ));
            process::exit(101);
        };

        let current_dir = std::env::current_dir();

        let package_index = metadata
            .packages
            .iter()
            .position(|package| {
                let package_manifest_path = Path::new(&package.manifest_path);
                if let Some(ref manifest_path) = manifest_path {
                    package_manifest_path == manifest_path
                } else {
                    let current_dir = current_dir.as_ref().expect(
                        "could not read current directory",
                    );
                    let package_manifest_dir = package_manifest_path
                        .parent()
                        .expect(
                            "could not find parent directory of package manifest",
                        );
                    package_manifest_dir == current_dir
                }
            })
            .expect("could not find matching package");
        let package = metadata.packages.remove(package_index);
        for target in package.targets {
            let args = env::args().skip(skip);
            let kind = target.kind.get(0).expect(
                "bad cargo metadata: target::kind is an empty array",
            );
            let mut process_args_opt = None;

            if test && kind == "test" {
                process_args_opt = Some(vec!["--test".to_string(), target.name]);
            } else if !test && kind == "bin" {
                process_args_opt = Some(vec!["--bin".to_string(), target.name]);
            } else if !test && kind == "lib" {
                process_args_opt = Some(vec!["--lib".to_string()]);
            } else {
                println!("Skipping target {}", &target.name)
            }

            if let Some(process_args) = process_args_opt {
                if let Err(code) = process(process_args.into_iter().chain(args)) {
                    process::exit(code);
                }
            }
        }
    } else {
        // this arm is executed when cargo-mir-json runs `cargo rustc`
        // with the `RUSTC` env var set to itself

        let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
        let toolchain = option_env!("RUSTUP_TOOLCHAIN")
                        .or(option_env!("MULTIRUST_TOOLCHAIN"));
        let sys_root = if let (Some(home), Some(toolchain)) = (home, toolchain) {
            format!("{}/toolchains/{}", home, toolchain)
        } else {
            option_env!("RUST_SYSROOT")
                .map(|s| s.to_owned())
                .or_else(|| {
                    Command::new("rustc")
                        .arg("--print")
                        .arg("sysroot")
                        .output()
                        .ok()
                        .and_then(|out| String::from_utf8(out.stdout).ok())
                        .map(|s| s.trim().to_owned())
                })
                .expect("need to specify RUST_SYSROOT env var during mir-json compilation, or use rustup or multirust")
        };

        // this conditional check for the --sysroot flag is there so
        // users can call `cargo-mir-json` directly without having to pass
        // --sysroot or anything
        let mut args: Vec<String> = if env::args().any(|s| s == "--sysroot") {
            env::args().skip(1).collect()
        } else {
            env::args()
                .skip(1)
                .chain(Some("--sysroot".to_owned()))
                .chain(Some(sys_root))
                .collect()
        };

        // this check ensures that dependencies are built but not
        // dumped and the final crate is dumped but not built
        // TODO: how does this impact mir-json?
        let mir_json_enabled = env::args().any(|s| s == "-Zno-trans");

        let mut command = if mir_json_enabled {
            let mut path = env::current_exe().expect(
                "current executable path invalid"
            );
            path.set_file_name("mir-json");
            Command::new(path)
        } else {
            Command::new("rustc")
        };

        args.extend_from_slice(&[
            "-Z".to_owned(),
            "always-encode-mir".to_owned()
        ]);

        match command.args(&args).status() {
            Ok(exit) => {
                if !exit.success() {
                    process::exit(exit.code().unwrap_or(42));
                }
            }
            Err(ref e) if mir_json_enabled => {
                panic!("error during mir-json run: {:?}", e)
            }
            Err(ref e) => {
                panic!("error during rustc call: {:?}", e)
            }
        }
    }
}

fn process<I>(old_args: I) -> Result<(), i32>
where
    I: Iterator<Item = String>,
{
    let mut args = vec!["rustc".to_owned()];

    let mut found_dashes = false;
    for arg in old_args {
        found_dashes |= arg == "--";
        args.push(arg);
    }
    if !found_dashes {
        args.push("--".to_owned());
    }
    args.push("-Zno-trans".to_owned());

    let path = env::current_exe().expect("current executable path invalid");
    let exit_status = std::process::Command::new("cargo")
        .args(&args)
        .env("RUSTC", path)
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
