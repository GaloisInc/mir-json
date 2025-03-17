//! `cargo crux-test`: Run symbolic tests of the current crate.
//!
//! Symbolic tests are identified by the `#[crux::test]` attribute, analogous to the `#[test]`
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
extern crate rustc_driver;
extern crate rustc_session;
extern crate serde;
extern crate serde_json;
extern crate toml_edit;

mod cargo_test_common;
use cargo_test_common::*;

fn main() {
    cargo_test_common("crux-test",
                      "Execute all symbolic unit tests of a local package",
                      &Vec::new(),
                      &Vec::new());
}
