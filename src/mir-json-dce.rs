//! Crude dead code elimination for .mir JSON files.
//!
//! This program takes in several .mir files, combines them, then runs dead code elimination with
//! `#[crux_test]`s as the roots.  This is useful because library .mir files contain entries for
//! all "reachable non-generic" items in the library crate, but some of those items are not
//! actually used by the top-level crate.  We run this pass on the raw JSON in hopes of removing
//! constructs that `mir-verifier` can't yet parse.
#![feature(rustc_private)]

extern crate serde;
#[macro_use] extern crate serde_derive;
#[macro_use] extern crate serde_json;
#[macro_use] extern crate log;

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io;
use std::mem;
use std::sync::atomic::{self, AtomicUsize};
use serde::{Deserialize, Deserializer};
use serde_json::Value as JsonValue;



#[derive(Deserialize, Default)]
pub struct Collection {
    #[serde(deserialize_with = "index_by_name")]
    fns: HashMap<String, JsonValue>,
    #[serde(deserialize_with = "index_by_name")]
    adts: HashMap<String, JsonValue>,
    #[serde(deserialize_with = "index_by_name")]
    statics: HashMap<String, JsonValue>,
    #[serde(deserialize_with = "index_by_name")]
    vtables: HashMap<String, JsonValue>,
    #[serde(deserialize_with = "index_by_name")]
    traits: HashMap<String, JsonValue>,
    #[serde(deserialize_with = "index_by_name")]
    intrinsics: HashMap<String, JsonValue>,
    roots: HashSet<String>,
}

fn index_by_name<'de, D: Deserializer<'de>>(de: D) -> Result<HashMap<String, JsonValue>, D::Error> {
    let j: JsonValue = Deserialize::deserialize(de)?;
    let arr = match j {
        JsonValue::Array(x) => x,
        _ => Err(serde::de::Error::custom("expected a json array"))?,
    };
    let mut m = HashMap::with_capacity(arr.len());
    for jj in arr {
        let name = match jj["name"] {
            JsonValue::String(ref name) => name.clone(),
            _ => Err(serde::de::Error::custom("expected `name` to be a json string"))?,
        };
        if m.contains_key(&name) {
            Err(serde::de::Error::custom(format_args!("duplicate entry for `{}`", name)))?
        }
        m.insert(name, jj);
    }
    Ok(m)
}


fn eq_filtered(a: &JsonValue, b: &JsonValue) -> bool {
    match (a, b) {
        (&JsonValue::Array(ref aa), &JsonValue::Array(ref ba)) => {
            aa.len() == ba.len() && aa.iter().zip(ba.iter()).all(|(a, b)| eq_filtered(a, b))
        },
        (&JsonValue::Object(ref am), &JsonValue::Object(ref bm)) => {
            if am.len() != bm.len() {
                return false;
            }
            for (k, av) in am.iter() {
                let bv = match bm.get(k) {
                    Some(x) => x,
                    None => return false,
                };

                // Ignore different file paths inside `pos` strings.
                if k == "pos" && av.as_str().is_some() && bv.as_str().is_some() {
                    continue;
                }

                if !eq_filtered(av, bv) {
                    return false;
                }
            }
            true
        },
        (_, _) => a == b,
    }
}

fn join_maps(this: &mut HashMap<String, JsonValue>, other: HashMap<String, JsonValue>) {
    this.reserve(other.len());
    for (k, v) in other {
        if let Some(old_v) = this.get(&k) {
            if !eq_filtered(old_v, &v) {
                panic!("\
                    different entries for `{}` appear in multiple sources\n\
                    old entry: {}\n\
                    new entry: {}\n", k, old_v, v);
            }
        }
        this.insert(k, v);
    }
}

fn join_sets(this: &mut HashSet<String>, other: HashSet<String>) {
    this.reserve(other.len());
    for k in other {
        if this.contains(&k) {
            panic!("entries for `{}` appear in multiple sources", k);
        }
        this.insert(k);
    }
}

fn sort_map<V>(mut m: HashMap<String, V>) -> Vec<V> {
    let mut keys = m.keys().cloned().collect::<Vec<_>>();
    keys.sort();
    keys.into_iter().map(|k| m.remove(&k).unwrap()).collect()
}

fn sort_set(s: HashSet<String>) -> Vec<String> {
    let mut v = s.into_iter().collect::<Vec<_>>();
    v.sort();
    v
}

impl Collection {
    pub fn add_all(&mut self, other: Collection) {
        let Collection { fns, adts, statics, vtables, traits, intrinsics, roots } = other;
        join_maps(&mut self.fns, fns);
        join_maps(&mut self.adts, adts);
        join_maps(&mut self.statics, statics);
        join_maps(&mut self.vtables, vtables);
        join_maps(&mut self.traits, traits);
        join_maps(&mut self.intrinsics, intrinsics);
        join_sets(&mut self.roots, roots);
    }

    pub fn to_json(self) -> JsonValue {
        json!({
            "fns": sort_map(self.fns),
            "adts": sort_map(self.adts),
            "statics": sort_map(self.statics),
            "vtables": sort_map(self.vtables),
            "traits": sort_map(self.traits),
            "intrinsics": sort_map(self.intrinsics),
            "impls": [],
            "roots": sort_set(self.roots),
        })
    }

    pub fn all_keys<'a>(&'a self) -> impl Iterator<Item = &'a String> + 'a {
        self.fns.keys()
            .chain(self.adts.keys())
            .chain(self.statics.keys())
            .chain(self.vtables.keys())
            .chain(self.traits.keys())
            .chain(self.intrinsics.keys())
    }

    pub fn all_values_for_key<'a>(&'a self, k: &str) -> impl Iterator<Item = &'a JsonValue> + 'a {
        self.fns.get(k).into_iter()
            .chain(self.adts.get(k).into_iter())
            .chain(self.statics.get(k).into_iter())
            .chain(self.vtables.get(k).into_iter())
            .chain(self.traits.get(k).into_iter())
            .chain(self.intrinsics.get(k).into_iter())
    }

    pub fn all_retain(&mut self, f: &mut FnMut(&str, &JsonValue) -> bool) {
        self.fns.retain(|k, v| f(k, v));
        self.adts.retain(|k, v| f(k, v));
        self.statics.retain(|k, v| f(k, v));
        self.vtables.retain(|k, v| f(k, v));
        self.traits.retain(|k, v| f(k, v));
        self.intrinsics.retain(|k, v| f(k, v));
    }

    pub fn iter_json_values<'a>(&'a self) -> impl Iterator<Item = &'a JsonValue> + 'a {
        self.fns.values()
            .chain(self.adts.values())
            .chain(self.statics.values())
            .chain(self.vtables.values())
            .chain(self.traits.values())
            .chain(self.intrinsics.values())
    }
}


fn read_inputs() -> io::Result<Vec<Collection>> {
    env::args().skip(1).map(|arg| -> io::Result<_> {
        let f = io::BufReader::new(File::open(&arg)?);
        Ok(serde_json::de::from_reader::<_, Collection>(f)?)
    }).collect()
}


fn has_keys(m: &serde_json::Map<String, JsonValue>, keys: &[&str]) -> bool {
    keys.iter().all(|&k| m.contains_key(k))
}

fn has_keys_exact(m: &serde_json::Map<String, JsonValue>, keys: &[&str]) -> bool {
    m.len() == keys.len() && has_keys(m, keys)
}

#[derive(Clone, Copy, Debug)]
enum DefKind<'a> {
    Instance(&'a JsonValue),
    Name(&'a str),
}

static COUNT: AtomicUsize = AtomicUsize::new(0);

fn test_walk<'a>(j: &'a JsonValue, depth: usize, emit: &mut impl FnMut(DefKind<'a>)) {
    match *j {
        JsonValue::Array(ref js) => {
            for j in js {
                test_walk(j, depth + 1, emit);
            }
        },
        JsonValue::String(ref s) => {
            if s.contains("::") {
                emit(DefKind::Name(s));
            }
        },
        JsonValue::Object(ref m) => {
            for (k, v) in m {
                test_walk(v, depth + 1, emit);
            }
        },
        _ => {},
    }
}


fn main() {
    let collections = read_inputs().unwrap();

    let mut coll = Collection::default();
    for c in collections {
        coll.add_all(c);
    }

    let all_keys = coll.all_keys().cloned().collect::<HashSet<_>>();
    let mut seen_keys = coll.roots.clone();
    let mut new_keys = coll.roots.clone();

    while !new_keys.is_empty() {
        trace!("process {} new keys", new_keys.len());
        for key in mem::replace(&mut new_keys, HashSet::new()) {
            for j in coll.all_values_for_key(&key) {
                test_walk(j, 0, &mut |def| match def {
                    DefKind::Name(name) => {
                        let name = name;
                        if all_keys.contains(name) {
                            if seen_keys.insert(name.to_owned()) {
                                new_keys.insert(name.to_owned());
                            }
                        }

                        if let Some(idx) = name.rfind("::") {
                            let prefix_name = &name[..idx];
                            if all_keys.contains(prefix_name) {
                                if seen_keys.insert(prefix_name.to_owned()) {
                                    new_keys.insert(prefix_name.to_owned());
                                }
                            }
                        }
                    },
                    _ => {},
                });
            }
        }
    }

    coll.all_retain(&mut |name, _| seen_keys.contains(name));

    debug!("{} fns", coll.fns.len());
    debug!("{} adts", coll.adts.len());
    debug!("{} statics", coll.statics.len());
    debug!("{} vtables", coll.vtables.len());
    debug!("{} traits", coll.traits.len());
    debug!("{} intrinsics", coll.intrinsics.len());
    debug!("{} roots", coll.roots.len());
    debug!("found {} reachable keys", seen_keys.len());

    let j = coll.to_json();
    serde_json::to_writer(io::stdout(), &j).unwrap();
}
