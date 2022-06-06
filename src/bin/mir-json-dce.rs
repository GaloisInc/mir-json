//! Crude dead code elimination for .mir JSON files.
//!
//! This program takes in several .mir files, combines them, then runs dead code elimination with
//! `#[crux_test]`s as the roots.  This is useful because library .mir files contain entries for
//! all "reachable non-generic" items in the library crate, but some of those items are not
//! actually used by the top-level crate.  We run this pass on the raw JSON in hopes of removing
//! constructs that `mir-verifier` can't yet parse.
#![feature(rustc_private)]

extern crate serde;
extern crate serde_cbor;
#[macro_use] extern crate log;
extern crate mir_json;
extern crate rustc_log;

use std::env;
use std::fs::File;
use std::io;
use std::time::Instant;
use mir_json::link;



fn main() {
    rustc_log::init_env_logger("RUST_LOG").unwrap();

    let mut last_time = Instant::now();
    let mut measure = || {
        let now = Instant::now();
        let dur = now.duration_since(last_time);
        last_time = now;
        dur
    };

    let mut inputs = env::args().skip(1).map(|arg| File::open(&arg))
        .collect::<io::Result<Vec<_>>>().unwrap();
    let output = io::BufWriter::new(io::stdout());
    link::link_crates(&mut inputs, output).unwrap();
    debug!("{:?}: link crates", measure());
}
