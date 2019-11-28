use std::collections::{HashMap, HashSet};
use std::io::{self, Read, Write, Seek, SeekFrom};

use serde_cbor::Value as CborValue;
use serde_json::Value as JsonValue;
use serde_cbor;
use serde_json;

use crate::lib_util::{self, InternTable, EntryKind, StringId};


/// Combine the contents of `ocs`, producing a combined JSON crate data object as the result.
pub fn link_crates<R, W>(inputs: &mut [R], mut output: W) -> serde_cbor::Result<()>
where R: Read + Seek, W: Write {
    let mut indexes = Vec::with_capacity(inputs.len());
    let mut json_offsets = Vec::with_capacity(inputs.len());
    for r in inputs.iter_mut() {
        let (i, j) = lib_util::read_crate_index(r)?;
        indexes.push(i);
        json_offsets.push(j);
    }


    // Assign global IDs to all items.
    let mut it = InternTable::default();
    // Gives the crate indexes and local IDs where each global name has been defined.
    let mut defs: HashMap<StringId, Vec<(usize, StringId)>> = HashMap::new();
    // Map from crate-local interned StringIds to global ones.
    let mut translate: HashMap<(usize, StringId), StringId> = HashMap::new();

    for (crate_num, index) in indexes.iter().enumerate() {
        for (local_id, name) in index.names.iter().enumerate() {
            let id = it.intern(name.into());
            translate.insert((crate_num, local_id), id);

            let item = match index.items.get(&local_id) {
                Some(x) => x,
                None => continue,
            };
            defs.entry(id).or_insert_with(Vec::new).push((crate_num, local_id));
        }
    }


    // Collect live items.
    let mut roots = Vec::new();
    for (crate_num, index) in indexes.iter().enumerate() {
        for &local_id in &index.roots {
            roots.push(translate[&(crate_num, local_id)]);
        }
    }

    let mut seen_names = HashSet::new();
    let mut worklist = roots.clone();
    while let Some(id) = worklist.pop() {
        // Look for deps in all crates.  It seems like different sets of entries for an item can
        // appear in different crates, though I'm not sure why.
        let def_list = match defs.get(&id) {
            Some(x) => x,
            None => continue,
        };
        for &(crate_num, local_id) in def_list {
            for &local_id2 in &indexes[crate_num].items[&local_id].deps {
                let id2 = translate[&(crate_num, local_id2)];
                if seen_names.insert(id2) {
                    worklist.push(id2);
                }
            }
        }
    }


    // Set up the tables that will be written to the output.
    let mut output_tables = vec![Vec::new(); 6];
    for &id in &seen_names {
        let mut saw_entry = [false; 6];
        // Check each input crate that defines the item, in case it has additional entries not
        // present in other crates.
        let def_list = match defs.get(&id) {
            Some(x) => x,
            None => continue,
        };
        for &(crate_num, local_id) in def_list {
            for (&kind, &(offset, len)) in &indexes[crate_num].items[&local_id].locations {
                if saw_entry[kind as usize] {
                    continue;
                }
                saw_entry[kind as usize] = true;

                let abs_offset = json_offsets[crate_num] + offset;
                output_tables[kind as usize].push((crate_num, abs_offset, len));
            }
        }
    }


    // Write tables to the output, copying the serialized content of each entry.
    write!(output, "{{")?;
    for (i, kind) in EntryKind::each().enumerate() {
        if i > 0 {
            write!(output, ",")?;
        }
        write!(output, "\"{}\":[", kind.table_name())?;
        output_tables[kind as usize].sort();
        for (j, &(crate_num, offset, len)) in output_tables[kind as usize].iter().enumerate() {
            if j > 0 {
                write!(output, ",")?;
            }

            let input = &mut inputs[crate_num];
            input.seek(SeekFrom::Start(offset))?;
            io::copy(&mut input.take(len), &mut output)?;
        }
        write!(output, "]")?;
    }
    write!(output, ",")?;
    write!(output, "\"impls\":[]")?;
    write!(output, ",")?;
    write!(output, "\"roots\":[")?;
    for (i, &id) in roots.iter().enumerate() {
        if i > 0 {
            write!(output, ",")?;
        }
        let name = it.name(id);
        serde_json::to_writer(&mut output, name)
            .map_err(|e| -> io::Error { e.into() })?;
    }
    write!(output, "]")?;
    write!(output, "}}")?;

    Ok(())
}
