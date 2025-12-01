//! `cargo saw-build`: Compile a MIR JSON file for SAW verification purposes.
//!
//! Despite the name, this is actually a wrapper around `cargo test --no-run`,
//! not `cargo build`. This is because we need to produce a binary in order for
//! `mir-json-rustc-wrapper` to work, and building a test binary is a reliable
//! way to do so.
//!
//! Crucible-specific build options can be set in the `[package.metadata.crux]` section of
//! `Cargo.toml`.  Currently supported options:
//!
//!  * `use_override_crates` (list of strings): Use Crucible overrides for the named crates.  These
//!    crates will be hidden from their downstream dependencies, causing fallback to the
//!    verifier-friendly implementations shipped with Crux.

#![feature(rustc_private)]
extern crate cargo;
extern crate clap;
extern crate rustc_driver;
extern crate rustc_session;
extern crate serde_json;
extern crate toml;

mod cargo_test_common;
use cargo_test_common::*;

fn main() {
    cargo_test_common("saw-build",
                      "Build a MIR JSON file for SAW verification purposes",
                      &vec!["--no-run".to_owned()],
                      &vec![
                          ("EXPORT_ALL".to_owned(), "true".to_owned()),
                          ("MIR_JSON_BUILD_TARGET".to_owned(), "saw".to_owned())
                      ]);
}
