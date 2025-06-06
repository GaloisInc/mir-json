//! Simple helper that invokes `mir-json-rustc-wrapper` the same way it would be run by `cargo
//! crux-test`.  Useful for testing a single file, with `crux-rustc --test foo.rs`.

#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_session;

use std::env;
use std::os::unix::process::CommandExt;
use std::path::PathBuf;
use std::process::Command;
use rustc_session::config::host_tuple;

fn main() {
    let mut args = Vec::new();

    args.push("rustc".into());
    args.extend(env::args().skip(1));
    // XXX big hack: `--target` is the magic signal to `mir-json-rustc-wrapper` that it should
    // enable Crux-specific functionality.  If the user didn't set `--target` themselves, we set it
    // explicitly to its default value.
    if args.iter().position(|s| s == "--target").is_none() {
        args.push("--target".into());
        args.push(host_tuple().into());
    }

    let my_path = PathBuf::from(env::args_os().nth(0).unwrap());
    let wrapper_path = if let Some(dir) = my_path.parent() {
        dir.join("mir-json-rustc-wrapper")
    } else {
        PathBuf::from("mir-json-rustc-wrapper")
    };

    let e = Command::new(&wrapper_path)
        .args(&args)
        .exec();
    unreachable!("exec failed: {:?}", e);
}
