//! Utilities for manipulating libraries.
//!
//! Some libraries are quite large (core, std) and contain mostly dead code.  We'd like to prune
//! away all the dead code before handing off the MIR to mir-verifier.  This speeds up
//! mir-verifier's processing, and also keeps it from crashing if some of the dead library code
//! contains unsupported constructs.
//!
//! Due to the size of the libraries in question, and because the "linking"/DCE process has to run
//! on each test case in the mir-verifier test suite, we apply some optimizations to make it fast.
//!
//! * Libraries are stored in CBOR format.  The final output is still JSON, to keep compatibility
//!   with existing mir-verifier code, but all intermediate steps use CBOR for faster parsing.
//! * Item paths are interned during linking, to avoid costly string comparisons.
//! * Library CBORs are "pre-interned", using a name table stored alongside the main data.  This
//!   further reduces the size of the inputs.  Interned names get expanded back to strings only in
//!   the final step, once all dead code has been eliminated.
//! * The dependencies of each item are precomputed by mir-json and stored in the CBOR file.  This
//!   lets the linker/DCE tool identify dead code without examining the body of each live item.
//! * Serialization is done in two phases.  Each item is serialized to a bytestring, then the
//!   bytestrings and metadata are serialized into the output file.  This lets the DCE tool avoid
//!   deserializing dead items, which can be fairly large.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet, BTreeMap};
use std::mem;

use serde_cbor::Value as CborValue;
use serde_json::Value as JsonValue;
use serde_cbor;
use serde_json;
use serde_bytes::ByteBuf;

/// The optimized data format used in library CBOR files.
#[derive(Serialize, Deserialize, Debug, Default)]
pub struct OptimizedCrate {
    /// Gives the dependencies of each item.  Items are identified by their path/DefId.  If two
    /// items of different kinds have the same name (e.g., an entry in "statics" and its matching
    /// entry in "fns"), the dependencies of both are merged when constructing this map.
    pub deps: HashMap<StringId, Vec<StringId>>,

    /// Name table.  `StringId`s in this `OptimizedCrate` are references into this table.
    pub names: Vec<String>,

    /// The actual crate data.  This is the JSON object produced by `analyz`, with a few
    /// transformations applied:
    ///
    /// * The JSON object is converted to equivalent CBOR.
    /// * Item paths are interned.  Each string containing `::` is replaced with a single-item map
    ///   `{0: string_id}`, where `string_id` is an index into the `names` table.  Since maps with
    ///   integer keys cannot appear in JSON, this encoding is unambiguous.
    /// * Each of the top-level data arrays (`fns`, `statics`, etc) is converted to a map.  For
    ///   each entry `{ "name": {0: string_id}, ... }` in the original table, the map contains an
    ///   entry whose key is `string_id` and whose value is a bytestring containing the CBOR
    ///   serialization of the entire entry.
    pub data: OptimizedCrateData,
}

#[derive(Serialize, Deserialize, Debug, Default)]
pub struct OptimizedCrateData {
    /// Map from function names to serialized CBOR data.
    pub fns: HashMap<StringId, ByteBuf>,
    pub adts: HashMap<StringId, ByteBuf>,
    pub statics: HashMap<StringId, ByteBuf>,
    pub vtables: HashMap<StringId, ByteBuf>,
    pub traits: HashMap<StringId, ByteBuf>,
    pub intrinsics: HashMap<StringId, ByteBuf>,
    pub roots: Vec<StringId>,
}


// JSON <-> CBOR conversions

pub fn json_to_cbor(j: JsonValue) -> CborValue {
    serde_cbor::value::to_value(j).unwrap()
}

pub fn cbor_to_json(c: CborValue) -> JsonValue {
    serde_cbor::value::from_value(c).unwrap()
}


// String interning

pub type StringId = usize;

#[derive(Default, Debug)]
pub struct InternTable {
    names: Vec<String>,
    map: HashMap<String, StringId>,
}

impl InternTable {
    pub fn intern(&mut self, s: Cow<str>) -> usize {
        if let Some(&i) = self.map.get(&s as &str) {
            return i;
        }

        let i = self.names.len();
        self.names.push((*s).to_owned());
        self.map.insert(s.into_owned(), i);
        i
    }

    pub fn name(&self, id: StringId) -> &str {
        &self.names[id]
    }

    pub fn into_names(self) -> Vec<String> {
        self.names
    }

    pub fn intern_strings_filtered(&mut self, c: &mut CborValue, f: &mut impl FnMut(&str) -> bool) {
        if let CborValue::Text(ref s) = *c {
            if f(s) {
                *c = make_interned_string(self.intern(s.into()));
            }
            return;
        }

        match *c {
            CborValue::Array(ref mut a) => {
                for x in a {
                    self.intern_strings_filtered(x, f);
                }
            },

            CborValue::Map(ref mut m) => {
                for x in m.values_mut() {
                    self.intern_strings_filtered(x, f);
                }
            },

            _ => {},
        }
    }
}

/// Try to extract the StringId from an interned string representation.  The input is expected to
/// be a map such as `{0: id}` - if it isn't, this function returns `None`.
pub fn parse_interned_string(c: &CborValue) -> Option<StringId> {
    let m = match *c {
        CborValue::Map(ref m) => m,
        _ => return None,
    };

    if m.len() != 1 {
        return None;
    }

    match m.get(&CborValue::Integer(0)) {
        Some(&CborValue::Integer(id)) => Some(id as usize),
        _ => None,
    }
}

pub fn make_interned_string(id: StringId) -> CborValue {
    let mut m = BTreeMap::new();
    m.insert(CborValue::Integer(0), CborValue::Integer(id as i128));
    m.into()
}

pub fn unintern_strings(names: &[String], c: &mut CborValue) {
    if let Some(id) = parse_interned_string(c) {
        *c = CborValue::Text(names[id as usize].clone());
        return;
    }

    match *c {
        CborValue::Array(ref mut a) => {
            for x in a {
                unintern_strings(names, x);
            }
        },

        CborValue::Map(ref mut m) => {
            for x in m.values_mut() {
                unintern_strings(names, x);
            }
        },

        _ => {},
    }
}

pub fn for_each_interned_string(c: &CborValue, f: &mut impl FnMut(StringId)) {
    if let Some(id) = parse_interned_string(c) {
        f(id);
        return;
    }

    match *c {
        CborValue::Array(ref a) => {
            for x in a {
                for_each_interned_string(x, f);
            }
        },

        CborValue::Map(ref m) => {
            for x in m.values() {
                for_each_interned_string(x, f);
            }
        },

        _ => {},
    }
}


// Dependency collection

fn iter_data_tables<'a>(
    c: &'a CborValue,
) -> impl Iterator<Item = (&'a str, &'a CborValue)> {
    let m = match *c {
        CborValue::Map(ref m) => m,
        _ => panic!("expected map at top level"),
    };

    m.iter().map(|(k, v)| {
        let name = match *k {
            CborValue::Text(ref s) => s,
            _ => panic!("expected map keys to be strings"),
        };
        (name as &str, v)
    })
}

fn iter_data_tables_mut<'a>(
    c: &'a mut CborValue,
) -> impl Iterator<Item = (&'a str, &'a mut CborValue)> {
    let m = match *c {
        CborValue::Map(ref mut m) => m,
        _ => panic!("expected map at top level"),
    };

    m.iter_mut().map(|(k, v)| {
        let name = match *k {
            CborValue::Text(ref s) => s,
            _ => panic!("expected map keys to be strings"),
        };
        (name as &str, v)
    })
}

/// Collect dependencies in `c`, which should be a crate data object with names already interned.
/// For each entry `{"name": {0: id}, ...}` in the top-level arrays of `c`, the output will contain
/// an entry for `id` containing the IDs of all interned strings that appear in the entry.  If
/// multiple arrays contain entries with the same name, their dependency sets will be merged.
pub fn gather_deps(c: &CborValue) -> HashMap<StringId, HashSet<StringId>> {
    let mut deps = HashMap::new();

    let name_str = CborValue::Text("name".to_owned());

    for (k, v) in iter_data_tables(c) {
        let a = match *v {
            CborValue::Array(ref a) => a,
            _ => continue,
        };

        for entry in a {
            let m = match *entry {
                CborValue::Map(ref m) => m,
                _ => continue,
            };

            let name_id = match m.get(&name_str).and_then(parse_interned_string) {
                Some(x) => x,
                _ => continue,
            };

            let mut v_deps = deps.entry(name_id).or_insert_with(HashSet::new);
            for_each_interned_string(entry, &mut |id| { v_deps.insert(id); });
        }
    }

    deps
}

pub fn convert_deps(
    m: HashMap<StringId, HashSet<StringId>>,
) -> HashMap<StringId, Vec<StringId>> {
    m.into_iter()
        .map(|(k, v)| (k, v.into_iter().collect::<Vec<_>>()))
        .collect::<HashMap<_, _>>()
}


// Serialization of data items

/// Serialize all items in `c` to bytestrings.  `c` should be a crate data object with strings
/// already interned.  This function replaces each top-level array with a map from names to
/// serialized bytestrings.
pub fn serialize_items(c: &mut CborValue) -> serde_cbor::Result<()> {
    let name_str = CborValue::Text("name".to_owned());

    for (k, v) in iter_data_tables_mut(c) {
        let a = match *v {
            CborValue::Array(ref mut a) => a,
            _ => panic!("expected an array for key `{}`", k),
        };

        if k == "roots" {
            // Convert `[{0: id1}, {0: id2}, ...]` to `[id1, id2, ...]`.
            for (i, x) in a.iter_mut().enumerate() {
                let name_id = parse_interned_string(x)
                    .unwrap_or_else(|| panic!("failed to get name of {} item {}", k, i));
                *x = CborValue::Integer(name_id as i128);
            }
            continue;
        }

        // Convert `[{"name": {0: id1}, ...}, {"name": {0: id2}, ...}, ...]` to `{id1: bytes1, id2:
        // bytes2, ...}`.
        let mut map = BTreeMap::new();
        for (i, x) in a.iter_mut().enumerate() {
            let serialized = serde_cbor::to_vec(x)?;

            let m = match *x {
                CborValue::Map(ref mut m) => m,
                _ => panic!("expected {} item {} to be a map", k, i),
            };

            let name_id = m.get(&name_str)
                .and_then(parse_interned_string)
                .unwrap_or_else(|| panic!("failed to get name of {} item {}", k, i));

            let key = CborValue::Integer(name_id as i128);
            assert!(!map.contains_key(&key), "duplicate entry for name_id {} in {}", name_id, k);
            map.insert(key, CborValue::Bytes(serialized));
        }
        *v = map.into();
    }

    Ok(())
}

pub fn deserialize_items(c: &mut CborValue) -> serde_cbor::Result<()> {
    for (k, v) in iter_data_tables_mut(c) {
        if k == "roots" {
            let a = match *v {
                CborValue::Array(ref mut a) => a,
                _ => panic!("expected an array for key `{}`", k),
            };
            for (i, x) in a.iter_mut().enumerate() {
                let id = match *x {
                    CborValue::Integer(id) => id as usize,
                    _ => panic!("expected {}[{}] to be an integer", k, i),
                };
                *x = make_interned_string(id);
            }
            continue;
        }

        let m = match *v {
            CborValue::Map(ref mut m) => m,
            _ => panic!("expected a map for key `{}`", k),
        };

        let mut arr = Vec::with_capacity(m.len());

        for (kk, vv) in m {
            let b = match *vv {
                CborValue::Bytes(ref b) => b,
                _ => panic!("expected {}[{:?}] to be byte string", k, kk),
            };

            let deserialized: CborValue = serde_cbor::from_slice(b)?;
            arr.push(deserialized);
        }

        *v = arr.into();
    }

    Ok(())
}


// Conversion to and from the optimized format

pub fn optimize_crate(j: JsonValue) -> serde_cbor::Result<OptimizedCrate> {
    let mut c = json_to_cbor(j);
    let mut it = InternTable::default();
    it.intern_strings_filtered(&mut c, &mut |s| s.contains("::"));
    let deps = convert_deps(gather_deps(&c));
    serialize_items(&mut c)?;

    Ok(OptimizedCrate {
        deps,
        names: it.into_names(),
        data: serde_cbor::value::from_value(c)?,
    })
}

pub fn deoptimize_crate(oc: OptimizedCrate) -> serde_cbor::Result<JsonValue> {
    let mut c = serde_cbor::value::to_value(oc.data)?;
    deserialize_items(&mut c)?;
    unintern_strings(&oc.names, &mut c);
    Ok(cbor_to_json(c))
}


// Helpers for use in linking

impl OptimizedCrate {
    pub fn decode_item(&self, b: &[u8]) -> serde_cbor::Result<JsonValue> {
        let mut c: CborValue = serde_cbor::from_slice(b)?;
        unintern_strings(&self.names, &mut c);
        Ok(cbor_to_json(c))
    }
}

impl OptimizedCrateData {
    pub fn all_tables<'a>(
        &'a self,
    ) -> Vec<&'a HashMap<StringId, ByteBuf>> {
        // Note: the order and number of items here must match `JsonCrate::iter_tables`.
        vec![
            &self.fns,
            &self.adts,
            &self.statics,
            &self.vtables,
            &self.traits,
            &self.intrinsics,
        ]
    }
}
