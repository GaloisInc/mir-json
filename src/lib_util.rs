//! Utilities for manipulating libraries.
//!
//! The canonical representation of a crate is the JSON format produced by `analyz`.  However, for
//! some large libraries (mainly `core` and `std`), the JSON representation can get quite large and
//! expensive to parse, with most of its contents being unused.  This module defines an alternate
//! representation that supports cheap dead code elimination, to minimize the amount of library
//! code that needs to be parsed.
//!
//! The "indexed library format" is a TAR archive containing two files:
//!
//!  * `crate.json` contains the JSON representation of the crate.
//!  * `index.cbor` contains metadata about the items in the crate.  Specifically, it lists the
//!    name and dependencies of each item, along with the position in `crate.json` where the JSON
//!    representation of the item can be found.
//!
//! The `link` module can use the index data of all crates in the program to perform whole-program
//! dead code elimination, without needing to read or parse any items up front.  Once the set of
//! live items is known, those items can be copied directly into the output JSON without parsing.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet, BTreeMap};
use std::io::{self, Read, Write, Seek, SeekFrom, Cursor};
use std::mem;
use std::path::Path;
use std::sync::mpsc::{self, SyncSender, Receiver};
use std::thread;

use serde_cbor::Value as CborValue;
use serde_json::Value as JsonValue;
use serde_cbor;
use serde_json;
use tar;

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct CrateIndex {
    /// Name table.  Contains every string in the crate that looks like it might be an item name.
    /// `StringId`s are indexes into this table.
    pub names: Vec<String>,

    pub items: HashMap<StringId, ItemData>,

    pub roots: Vec<StringId>,
}

/// Metadata about a single item.
///
/// An item may have entries in multiple tables.  For example, a `static` item will have entries in
/// both the `statics` and `fns` tables (with the `fns` entry being the static's initializer).  All
/// entries with the same name will be aggregated into a single item.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct ItemData {
    /// All names mentioned in the bodies of this item.
    pub deps: Vec<StringId>,

    /// The location of each entry for this item.  The first `u64` is the offset of the entry's
    /// JSON representation within `crates.json`, and the second `u64` is the length.
    pub locations: HashMap<EntryKind, (u64, u64)>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum EntryKind {
    Fn,
    Adt,
    Static,
    Vtable,
    Trait,
    Intrinsic,
}

impl EntryKind {
    pub fn table_name(self) -> &'static str {
        use self::EntryKind::*;
        match self {
            Fn => "fns",
            Adt => "adts",
            Static => "statics",
            Vtable => "vtables",
            Trait => "traits",
            Intrinsic => "intrinsics",
        }
    }

    pub fn each() -> impl Iterator<Item = EntryKind> {
        use self::EntryKind::*;
        [Fn, Adt, Static, Vtable, Trait, Intrinsic].iter().cloned()
    }
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
}


// IO adapter

/// Writer that keeps a count of the number of bytes written so far.
struct CountWrite<W> {
    w: W,
    count: usize,
}

impl<W: Write> Write for CountWrite<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let amt = self.w.write(buf)?;
        self.count += amt;
        Ok(amt)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}


// JSON serialization and indexing

struct Emitter<W> {
    dep_map: HashMap<StringId, HashSet<StringId>>,
    entry_loc: HashMap<(StringId, EntryKind), (u64, u64)>,
    roots: HashSet<StringId>,
    intern: InternTable,
    writer: CountWrite<W>,
}

impl<W: Write> Emitter<W> {
    pub fn new(w: W) -> Emitter<W> {
        Emitter {
            dep_map: Default::default(),
            entry_loc: Default::default(),
            roots: Default::default(),
            intern: Default::default(),
            writer: CountWrite { w, count: 0 },
        }
    }

    fn gather_deps(&mut self, id: StringId, j: &JsonValue) {
        match *j {
            JsonValue::Array(ref a) => {
                for x in a {
                    self.gather_deps(id, x);
                }
            },

            JsonValue::Object(ref m) => {
                for x in m.values() {
                    self.gather_deps(id, x);
                }
            },

            JsonValue::String(ref s) => {
                if s.contains("::") {
                    let id2 = self.intern.intern(s.into());
                    self.dep_map.entry(id).or_insert_with(HashSet::new).insert(id2);
                }
            },

            _ => {},
        }
    }

    fn emit_entry(&mut self, kind: EntryKind, j: &JsonValue) -> io::Result<()> {
        // Collect dependencies
        let name_id = self.intern.intern(j["name"].as_str().unwrap().into());
        self.gather_deps(name_id, j);

        // Serialize the entry, and record its position.
        let start = self.writer.count as u64;
        serde_json::to_writer(&mut self.writer, j)?;
        let end = self.writer.count as u64;
        let len = end - start;
        let old = self.entry_loc.insert((name_id, kind), (start, len));
        assert!(old.is_none(), "duplicate {:?} named {:?}", kind, self.intern.name(name_id));

        Ok(())
    }

    fn emit_table(&mut self, kind: EntryKind, j: &JsonValue) -> io::Result<()> {
        write!(self.writer, "\"{}\":[", kind.table_name())?;
        let a = j.as_array()
            .unwrap_or_else(|| panic!("expected {:?} table to be an array", kind));
        for (i, x) in a.iter().enumerate() {
            if i > 0 {
                write!(self.writer, ",")?;
            }
            self.emit_entry(kind, x)?;
        }
        write!(self.writer, "]")?;
        Ok(())
    }

    fn emit_table_from(&mut self, kind: EntryKind, j: &JsonValue) -> io::Result<()> {
        self.emit_table(kind, &j[kind.table_name()])
    }

    pub fn emit_crate(&mut self, j: &JsonValue) -> io::Result<()> {
        write!(self.writer, "{{")?;
        self.emit_table_from(EntryKind::Fn, j);
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Adt, j);
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Static, j);
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Vtable, j);
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Trait, j);
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Intrinsic, j);
        write!(self.writer, ",")?;
        write!(self.writer, "\"impls\":[]")?;
        write!(self.writer, ",")?;
        write!(self.writer, "\"roots\":")?;
        serde_json::to_writer(&mut self.writer, &j["roots"])?;
        write!(self.writer, "}}")?;
        self.writer.flush()?;

        let j_roots = j["roots"].as_array()
            .unwrap_or_else(|| panic!("expected \"roots\" table to be an array"));
        for x in j_roots {
            let name_id = self.intern.intern(x.as_str().unwrap().into());
            self.roots.insert(name_id);
        }

        Ok(())
    }

    pub fn finish(mut self) -> CrateIndex {
        let names = self.intern.into_names();

        let mut items = HashMap::with_capacity(self.dep_map.len());
        for (name, v) in self.dep_map {
            let mut data = items.entry(name).or_insert_with(ItemData::default);

            data.deps = v.into_iter().collect::<Vec<_>>();
            data.deps.sort();

            for kind in EntryKind::each() {
                if let Some(&loc) = self.entry_loc.get(&(name, kind)) {
                    data.locations.insert(kind, loc);
                }
            }
        }

        let mut roots = self.roots.into_iter().collect::<Vec<_>>();
        roots.sort();

        CrateIndex { names, items, roots }
    }
}

pub fn write_indexed_crate<W>(out: W, j: &JsonValue) -> serde_cbor::Result<()>
where W: Write + Send + 'static {
    // Serialize the two files to byte arrays.  This is needed so their lengths will be known when
    // creating the archive.
    let mut json_buf = Vec::new();
    let mut emitter = Emitter::new(&mut json_buf);
    emitter.emit_crate(j)?;

    let index = emitter.finish();
    let index_buf = serde_cbor::to_vec(&index)?;

    let mut tar = tar::Builder::new(out);
    tar.mode(tar::HeaderMode::Deterministic);

    let mut json_hdr = tar::Header::new_ustar();
    json_hdr.set_size(json_buf.len() as u64);
    json_hdr.set_mode(0o644);
    tar.append_data(&mut json_hdr, "crate.json", Cursor::new(json_buf))?;

    let mut index_hdr = tar::Header::new_ustar();
    index_hdr.set_size(index_buf.len() as u64);
    index_hdr.set_mode(0o644);
    tar.append_data(&mut index_hdr, "index.cbor", Cursor::new(index_buf))?;

    tar.finish()?;

    Ok(())
}

/// Read the crate index.  Also returns the byte offset of the start of `crate.json`, to avoid a
/// second scan over the archive.
pub fn read_crate_index<R: Read + Seek>(mut input: R) -> serde_cbor::Result<(CrateIndex, u64)> {
    input.seek(SeekFrom::Start(0))?;
    let mut tar = tar::Archive::new(input);

    let mut index = None;
    let mut json_offset = None;

    for entry in tar.entries()? {
        let entry = entry?;
        let path = entry.path()?;
        if path == Path::new("index.cbor") {
            assert!(index.is_none(), "duplicate crate.json in archive?");
            index = Some(serde_cbor::from_reader(entry)?);
        } else if path == Path::new("crate.json") {
            assert!(json_offset.is_none(), "duplicate crate.json in archive?");
            assert!(entry.header().size()? == entry.header().entry_size()?,
                "crate.json is a sparse file (unsupported)");
            json_offset = Some(entry.raw_file_position());
        }
    }

    let index = index.unwrap_or_else(|| panic!("index.cbor not found in archive"));
    let json_offset = json_offset.unwrap_or_else(|| panic!("crate.json not found in archive"));

    Ok((index, json_offset))
}
