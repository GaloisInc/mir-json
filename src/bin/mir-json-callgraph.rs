//! Usage: `mir-json-callgraph NAME CRATES...`
//!
//! Print the reverse callgraph of item `NAME`, after linking together `CRATES` as in
//! `mir-json-dce`.  Useful for figuring out how to prevent a function from being called, when
//! that function is causing crucible-mir translation errors.
#![feature(rustc_private)]

extern crate serde;
extern crate serde_cbor;
#[macro_use] extern crate serde_json;
extern crate mir_json;

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io;
use serde_json::Value as JsonValue;
use mir_json::lib_util::{StringId, InternTable};
use mir_json::link;
use mir_json::version;

fn main() {

    if version::has_flag(&mut std::env::args()) {
        version::show();
        return;
    }

    let root_name = env::args().nth(1).unwrap();
    let mut inputs = env::args().skip(2).map(|arg| File::open(&arg))
        .collect::<io::Result<Vec<_>>>().unwrap();
    let (mut it, calls) = link::gather_calls(&mut inputs).unwrap();

    let mut map = HashMap::new();
    for (a, b) in calls {
        if a == b {
            continue;
        }
        map.entry(b).or_insert_with(HashSet::new).insert(a);
    }

    let root = it.intern(root_name.clone().into());
    fn walk(
        it: &InternTable,
        map: &HashMap<StringId, HashSet<StringId>>,
        seen: &mut HashSet<StringId>,
        id: StringId,
    ) -> JsonValue {
        if seen.contains(&id) {
            return json!(null);
        }

        seen.insert(id);

        let callers = match map.get(&id) {
            Some(x) => x,
            None => return json!({}),
        };
        let mut m = serde_json::Map::new();
        for &id2 in callers {
            let k = it.name(id2).to_owned();
            let v = walk(it, map, seen, id2);
            m.insert(k, v);
        }

        seen.remove(&id);

        m.into()
    }

    let j = json!({
        root_name: walk(&it, &map, &mut HashSet::new(), root)
    });

    serde_json::to_writer(&mut io::stdout(), &j).unwrap();
}
