use std::collections::{HashMap, HashSet};

use serde_cbor::Value as CborValue;
use serde_json::Value as JsonValue;
use serde_cbor;
use serde_json;

use crate::lib_util::{OptimizedCrate, InternTable, StringId};


#[derive(Serialize, Default)]
pub struct JsonCrate {
    fns: Vec<JsonValue>,
    adts: Vec<JsonValue>,
    statics: Vec<JsonValue>,
    vtables: Vec<JsonValue>,
    traits: Vec<JsonValue>,
    intrinsics: Vec<JsonValue>,
    impls: Vec<JsonValue>,
    roots: Vec<String>,
}

impl JsonCrate {
    pub fn iter_tables<'a>(
        &'a mut self,
    ) -> impl Iterator<Item = &'a mut Vec<JsonValue>> {
        vec![
            &mut self.fns,
            &mut self.adts,
            &mut self.statics,
            &mut self.vtables,
            &mut self.traits,
            &mut self.intrinsics,
        ].into_iter()
    }
}


/// Combine the contents of `ocs`, producing a combined JSON crate data object as the result.
pub fn link_crates(ocs: &[OptimizedCrate]) -> serde_cbor::Result<JsonCrate> {
    let mut it = InternTable::default();
    // For each name in the global intern table, give the crate index and crate-local StringId of
    // each place where the name was found.
    let mut all_origins: HashMap<StringId, Vec<(usize, StringId)>> = HashMap::new();
    // Give a single origin to use for each global name.  We can choose arbitrarily from
    // `all_origins[id]` because we check at the end to ensure that all versions of an item are
    // equivalent.  And since they're equivalent, all their `deps` entries are equivalent too.
    let mut origin = Vec::new();
    // Map from crate-local interned StringIds to global ones.
    let mut translate: HashMap<(usize, StringId), StringId> = HashMap::new();

    for (k, oc) in ocs.iter().enumerate() {
        for (i, name) in oc.names.iter().enumerate() {
            let j = it.intern((name as &str).into());
            all_origins.entry(j).or_insert_with(|| Vec::with_capacity(1)).push((k, i));
            translate.insert((k, i), j);

            if j >= origin.len() {
                assert!(j == origin.len());
                // This is the first time we've seen this name in any crate.
                origin.push((k, i));
            }
        }
    }


    let mut roots = Vec::new();
    for (crate_idx, oc) in ocs.iter().enumerate() {
        roots.extend(oc.data.roots.iter().cloned()
            .map(|local_id| translate[&(crate_idx, local_id)]));
    }

    let mut seen_names = HashSet::new();
    let mut worklist = roots.clone();
    while let Some(id) = worklist.pop() {
        // Look for deps in all crates.  A name can appear in a crate's interning table when the
        // name is only referenced, in which case there will be no deps for it in that crate.
        for &(crate_idx, local_id) in &all_origins[&id] {
            // If this item has dependencies, add all deps that haven't been seen yet to the
            // worklist.
            if let Some(deps) = ocs[crate_idx].deps.get(&local_id) {
                for &local_id2 in deps {
                    let id2 = translate[&(crate_idx, local_id2)];
                    if seen_names.insert(id2) {
                        worklist.push(id2);
                    }
                }
            }
        }
    }


    let names = it.into_names();
    let mut jc = JsonCrate::default();
    jc.roots = roots.into_iter().map(|id| names[id].clone()).collect();

    let oc_tables = ocs.iter().map(|oc| oc.data.all_tables()).collect::<Vec<_>>();

    for &id in &seen_names {
        for (tbl_idx, jtbl) in jc.iter_tables().enumerate() {
            let (crate_idx0, local_id0) = origin[id];


            if all_origins[&id].len() == 1 {
                // Item `id` is mentioned somewhere in `crate_idx0`, but doesn't necessarily exist
                // in table `tbl_idx`.
                if let Some(b) = oc_tables[crate_idx0][tbl_idx].get(&local_id0) {
                    let entry = ocs[crate_idx0].decode_item(b)?;
                    jtbl.push(entry);
                }
                continue;
            }

            /*
            // The entry must either be present in all `ocs` tables, or absent in all of them.
            if !oc_tables[crate_idx0][tbl_idx].contains_key(&local_id0) {
                for &(crate_idx, local_id) in &all_origins[&id] {
                    if oc_tables[crate_idx][tbl_idx].contains_key(&local_id) {
                        panic!("item {} is present in table {} of crate {}",
                            names[id], tbl_idx, crate_idx);
                    }
                }
                continue;
            }

            let mut entries = all_origins[&id].iter().map(|&(crate_idx, local_id)| {
                let octbl = oc_tables[crate_idx][tbl_idx];
                if let Some(b) = octbl.get(&local_id) {
                    ocs[crate_idx].decode_item(b)
                } else {
                    panic!("item {} is absent in table {} of crate {}",
                        names[id], tbl_idx, crate_idx);
                }
            }).collect::<Result<Vec<_>, _>>()?;
            */

            let mut entries = all_origins[&id].iter().filter_map(|&(crate_idx, local_id)| {
                let octbl = oc_tables[crate_idx][tbl_idx];
                octbl.get(&local_id).map(|b| ocs[crate_idx].decode_item(b))
            }).collect::<Result<Vec<_>, _>>()?;

            // TODO: check that all entries are identical (ignoring spans/filenames)
            if let Some(entry) = entries.pop() {
                jtbl.push(entry);
            }
        }
    }


    Ok(jc)
}
