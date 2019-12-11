use std::env;
use std::path::PathBuf;
use std::process::{self, Command};

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
    // TODO: autodetect the default target.
    args.push("x86_64-unknown-linux-gnu".into());
    args.extend(orig_args.into_iter());

    let my_path = PathBuf::from(env::args_os().nth(0).unwrap());
    let wrapper_path = if let Some(dir) = my_path.parent() {
        dir.join("mir-json-rustc-wrapper")
    } else {
        PathBuf::from("mir-json-rustc-wrapper")
    };

    let status = Command::new(&cargo)
        .args(&args)
        .env("RUSTC_WRAPPER", wrapper_path)
        .status().unwrap();
    // `code` can return `None` if the process was terminated by a signal.  We return nonzero
    // ourselves in that case.
    process::exit(status.code().unwrap_or(1));
}

