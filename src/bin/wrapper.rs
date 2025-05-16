use std::env;
use std::fmt::Display;
use std::ffi::OsString;
use std::fs;
use std::iter;
use std::path::{Path, PathBuf};
use std::process::{self, Command};
use std::str;
use std::os::unix::process::CommandExt;

fn die(msg: impl Display) -> ! {
    eprintln!("{}", msg);
    process::exit(1);
}

macro_rules! die {
    ($($args:tt)*) => {
        die(format_args!($($args)*))
    };
}

const ALREADY_SET_VAR: &str = "CRUX_MIR_ALREADY_SET_PATH";

#[cfg(target_os = "linux")]
const LIB_PATH_VAR: &str = "LD_LIBRARY_PATH";
#[cfg(target_os = "macos")]
const LIB_PATH_VAR: &str = "DYLD_LIBRARY_PATH";

const TOOLCHAIN: &str = "nightly-2025-02-16";

fn find_lib_dir() -> PathBuf {
    let output = Command::new("rustc")
        .arg(format!("+{}", TOOLCHAIN))
        .arg("--print").arg("sysroot")
        .output()
        .unwrap_or_else(|e| die!("error running rustc: {}", e));

    if !output.status.success() {
        eprintln!("error finding toolchain sysroot");
        eprint!("{}", String::from_utf8_lossy(&output.stdout));
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
        eprintln!("");
        eprintln!(
            "note: this tool requires rustup toolchain `{}`; to install it, run:",
            TOOLCHAIN,
        );
        eprintln!(
            "    rustup toolchain install {} --force --component rustc-dev,rust-src",
            TOOLCHAIN);
        eprintln!("");
        eprintln!(
            "note: if you have configured PATH and {} manually, set {} to disable this check",
            LIB_PATH_VAR, ALREADY_SET_VAR,
        );
        process::exit(output.status.code().unwrap_or(1));
    }

    let path_str = str::from_utf8(&output.stdout)
        .unwrap_or_else(|e| die!(
            "rustc sysroot path {:?} is not valid utf-8: {}",
            output.stdout, e,
        ))
        .trim_end();

    let path = Path::new(path_str).join("lib");
    match fs::metadata(&path) {
        Ok(_) => {},
        Err(e) => die!("error accessing rustc library dir {:?}: {}", path, e),
    };
    path
}

fn build_library_path() -> OsString {
    let path_list = env::var_os(LIB_PATH_VAR).unwrap_or(OsString::new());
    let paths = env::split_paths(&path_list);
    env::join_paths(paths.chain(iter::once(find_lib_dir())))
        .unwrap_or_else(|e| die!("error building library path: {}", e))
}

fn main() {
    let mut args = env::args_os();
    let arg0 = args.next()
        .unwrap_or_else(|| die!("missing arg0"));

    let arg0 = Path::new(&arg0);
    let mut real_name = arg0.file_stem()
        .unwrap_or_else(|| die!("executable path {:?} has no filename?", arg0))
        .to_owned();
    real_name.push("_real");
    if let Some(ext) = arg0.extension() {
        real_name.push(".");
        real_name.push(ext);
    }

    let real_arg0 = arg0.with_file_name(real_name);

    let mut cmd = Command::new(&real_arg0);
    cmd.args(args);

    // If `ALREADY_SET_VAR` is already set, then a parent process has already set up the library
    // path in the environment, and we can directly exec the real process with no adjustments.
    let already_set_path = env::var_os(ALREADY_SET_VAR).is_some();
    if !already_set_path {
        cmd.env(LIB_PATH_VAR, build_library_path());
        cmd.env(ALREADY_SET_VAR, "1");
    }

    // Ensure the correct Rust toolchain is used at runtime
    cmd.env("RUSTUP_TOOLCHAIN", TOOLCHAIN);

    let e = cmd.exec();
    die!("error executing {:?}: {}", real_arg0, e);
}
