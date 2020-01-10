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
extern crate rustc;
extern crate serde_json;

use std::env;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process::{self, Command};
use rustc::session::config::host_triple;

fn get_root_metadata<'a>(j: &'a serde_json::Value) -> &'a serde_json::Value {
    let root_name = j["resolve"]["root"].as_str().unwrap();
    let packages = j["packages"].as_array().unwrap();
    for p in packages {
        if p["id"] == root_name {
            return &p["metadata"];
        }
    }
    panic!("root package {:?} not found", root_name);
}

fn get_override_crates(j: &serde_json::Value) -> Option<String> {
    // The `crux` key is allowed to be missing, but if present, it must be an object.
    let crux = j.get("crux")?;
    assert!(crux.is_object(), "expected `package.metadata.crux` to be an object");
    let overrides = crux.get("use_override_crates")?;
    assert!(overrides.is_array(), "expected `crux.use_override_crates` to be an array");
    let mut s = String::new();
    for x in overrides.as_array().unwrap() {
        assert!(x.is_string(), "expected `crux.use_override_crates` items to be strings");
        if s.len() > 0 {
            s.push(' ');
        }
        s.push_str(x.as_str().unwrap());
    }
    Some(s)
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
    // TODO: autodetect the default target.
    args.push(host_triple().into());
    args.extend(orig_args.into_iter());

    let my_path = PathBuf::from(env::args_os().nth(0).unwrap());
    let wrapper_path = if let Some(dir) = my_path.parent() {
        dir.join("mir-json-rustc-wrapper")
    } else {
        PathBuf::from("mir-json-rustc-wrapper")
    };

    let output = Command::new(&cargo)
        .arg("metadata")
        .args(&["--format-version", "1"])
        .output().unwrap();
    std::io::stderr().write_all(&output.stderr).unwrap();
    assert!(output.status.success());
    let all_metadata = serde_json::from_slice(&output.stdout).unwrap();
    let metadata = get_root_metadata(&all_metadata);
    eprintln!("{:?}", metadata);
    let override_crates = get_override_crates(&metadata).unwrap_or_else(String::new);

    let status = Command::new(&cargo)
        .args(&args)
        .env("RUSTC_WRAPPER", wrapper_path)
        .env("CRUX_USE_OVERRIDE_CRATES", override_crates)
        .status().unwrap();
    // `code` can return `None` if the process was terminated by a signal.  We return nonzero
    // ourselves in that case.
    process::exit(status.code().unwrap_or(1));
}

