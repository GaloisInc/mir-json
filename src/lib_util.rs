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
use std::convert::TryFrom;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::hash::Hash;
use std::io::{self, Write, Cursor, BufWriter};
use std::path::Path;
use rustc_middle::ty::{ TyCtxt};
use rustc_span::def_id::CrateNum;

use serde::ser;
use serde_json::Value as JsonValue;
use serde_cbor;
use serde_json;
use tar;

use crate::schema_ver::SCHEMA_VER;
use crate::tar_stream::{TarStream, TarEntryStream};

#[derive(Debug, Default, Serialize, Deserialize, Eq, PartialEq, PartialOrd, Ord, Hash, Clone)]
pub struct UniqueCrateId{
    /// The name of the crate (regardless of crate aliases)
    pub name: String,
    /// A unique identifier for this crate that is based on the
    /// Strict Version Hash (SVH). See how this struct is constructed
    /// for more details.
    pub hash: String,
}
impl std::fmt::Display for UniqueCrateId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Crate< name: {}, Svh Hash: {} >", self.name, self.hash)
    }
}

impl UniqueCrateId{
    pub fn new( tcx: TyCtxt, cnum: CrateNum) -> Self {
        //  Note that crate aliases demarking different versions of the
        //  same crate will have the same crate name but different crate
        //  hashes.  
        UniqueCrateId {    
            name: tcx.crate_name(cnum).to_string(),
            hash: tcx.crate_hash(cnum).to_string() 
        }
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct CrateDependencies{
    /// The crate's unique identifier 
    root_hash:UniqueCrateId,
    /// A hashset of unique identifiers for the crate's dependencies
    dep_hashes: HashSet<UniqueCrateId>
}

impl CrateDependencies{
    pub fn new( root_hash:UniqueCrateId, dep_hashes: HashSet<UniqueCrateId>) -> Self { 
        CrateDependencies {             
            root_hash,
            dep_hashes
        }
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct CrateIndex {
    /// Name table.  Contains every string in the crate that looks like it might be an item name.
    /// `StringId`s are indexes into this table.
    pub names: Vec<String>,

    pub items: HashMap<StringId, ItemData>,

    /// Translation roots
    pub roots: Vec<StringId>,

    /// Subsets of roots marked with crux-test
    pub tests: Vec<StringId>,

    /// The schema version in use. (See also `SCHEMA_VER`.)
    pub version: u64,
    /// Extra information that allows us to uniquely identify this crate and
    /// it's dependencies
    pub extra_data: CrateDependencies,
}

impl CrateIndex{
    pub fn root_hash(&self) -> UniqueCrateId{
        self.extra_data.root_hash.clone()
    }
    pub fn dep_hashes(&self) -> HashSet<UniqueCrateId>{
        self.extra_data.dep_hashes.clone()
    }
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
    pub locations: HashMap<EntryKind, (usize, usize)>,
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
    Ty,
    LangItem,
}

impl EntryKind {
    pub fn name(self) -> &'static str {
        use self::EntryKind::*;
        match self {
            Fn => "fn",
            Adt => "adt",
            Static => "static",
            Vtable => "vtable",
            Trait => "trait",
            Intrinsic => "intrinsic",
            Ty => "ty",
            LangItem => "lang_item",
        }
    }

    pub fn table_name(self) -> &'static str {
        use self::EntryKind::*;
        match self {
            Fn => "fns",
            Adt => "adts",
            Static => "statics",
            Vtable => "vtables",
            Trait => "traits",
            Intrinsic => "intrinsics",
            Ty => "tys",
            LangItem => "lang_items",
        }
    }

    pub fn each() -> impl Iterator<Item = EntryKind> {
        use self::EntryKind::*;
        // Type annotation ensures we have exactly `count()` entries.
        let all: &'static [EntryKind; Self::count()] =
            &[Fn, Adt, Static, Vtable, Trait, Intrinsic, Ty, LangItem];
        all.iter().cloned()
    }

    pub const fn count() -> usize {
        8
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

#[derive(Default)]
struct EmitterState {
    dep_map: HashMap<StringId, HashSet<StringId>>,
    entry_loc: HashMap<(StringId, EntryKind), (usize, usize)>,
    roots: HashSet<StringId>,
    tests: HashSet<StringId>,
    intern: InternTable,
}

impl EmitterState {
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

    fn emit_entry<E, F: FnOnce(EntryKind, &JsonValue) -> Result<(usize, usize), E>>(
        &mut self,
        kind: EntryKind,
        j: &JsonValue,
        write_entry: F,
    ) -> Result<(), E> {
        // Collect dependencies
        let name_id = self.intern.intern(j["name"].as_str().unwrap().into());
        self.gather_deps(name_id, j);

        // Serialize the entry, and record its position.
        let (start, end) = write_entry(kind, j)?;
        let len = end - start;
        let _old = self.entry_loc.insert((name_id, kind), (start, len));
        // FIXME - shouldn't allow multiple overlapping names, but `nix` has multiple versions of
        // `libc` in its dependency graph, and their types collide.  For now we let it go through
        // and just hope for the best
        //assert!(old.is_none(), "duplicate {:?} named {:?}", kind, self.intern.name(name_id));

        Ok(())
    }

    fn add_root(&mut self, s: Cow<str>, is_test: bool) {
        let name_id = self.intern.intern(s);
        self.roots.insert(name_id);
        if is_test { self.tests.insert(name_id); }
    }

    pub fn finish(self, extra_data: CrateDependencies) -> CrateIndex {
        let names = self.intern.into_names();

        let mut items = HashMap::with_capacity(self.dep_map.len());
        for (name, v) in self.dep_map {
            let data = items.entry(name).or_insert_with(ItemData::default);

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

        let mut tests = self.tests.into_iter().collect::<Vec<_>>();
        tests.sort();

        let version = SCHEMA_VER;

        CrateIndex { names, items, roots, tests, version, extra_data}
    }
}

struct Emitter<W> {
    state: EmitterState,
    writer: CountWrite<W>,
}

impl<W: Write> Emitter<W> {
    pub fn new(w: W) -> Emitter<W> {
        Emitter {
            state: EmitterState::default(),
            writer: CountWrite { w, count: 0 },
        }
    }

    fn emit_entry(&mut self, kind: EntryKind, j: &JsonValue) -> io::Result<()> {
        let writer = &mut self.writer;
        self.state.emit_entry(kind, j, |_, j| {
            let start = writer.count;
            serde_json::to_writer(&mut *writer, j)?;
            let end = writer.count;
            Ok((start, end))
        })
    }

    fn add_root(&mut self, name: Cow<str>, is_test: bool) {
        self.state.add_root(name, is_test);
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
        write!(self.writer, "\"version\":{:?},", SCHEMA_VER)?;
        self.emit_table_from(EntryKind::Fn, j)?;
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Adt, j)?;
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Static, j)?;
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Vtable, j)?;
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Trait, j)?;
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::Intrinsic, j)?;
        write!(self.writer, ",")?;
        self.emit_table_from(EntryKind::LangItem, j)?;
        write!(self.writer, ",")?;
        write!(self.writer, "\"roots\":")?;
        serde_json::to_writer(&mut self.writer, &j["roots"])?;
        write!(self.writer, ",")?;
        write!(self.writer, "\"tests\":")?;
        serde_json::to_writer(&mut self.writer, &j["tests"])?;
        write!(self.writer, "}}")?;
        self.writer.flush()?;

        let j_roots = j["roots"].as_array()
            .unwrap_or_else(|| panic!("expected \"roots\" table to be an array"));
        
        let j_tests = j["tests"].as_array()
            .unwrap_or_else(|| panic!("expected \"tests\" table to be an array"));

        let tests = j_tests.iter().collect::<HashSet<_>>();
        
        for x in j_roots {
            let is_test = tests.contains(x);
            self.add_root(x.as_str().unwrap().into(), is_test);
        }

        Ok(())
    }

    pub fn finish(self, extra_data: CrateDependencies) -> CrateIndex {
        self.state.finish(extra_data)
    }
}

pub fn write_indexed_crate<W>(out: W, j: &JsonValue, extra_data: CrateDependencies) -> serde_cbor::Result<()>
where W: Write + Send + 'static {
    // Serialize the two files to byte arrays.  This is needed so their lengths will be known when
    // creating the archive.
    let mut json_buf = Vec::new();
    let mut emitter = Emitter::new(&mut json_buf);
    emitter.emit_crate(j)?;

    let index = emitter.finish(extra_data);
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
pub fn read_crate_index(input: impl AsRef<[u8]>) -> serde_cbor::Result<(CrateIndex, usize)> {
    let input = input.as_ref();

    let mut index = None;
    let mut json_offset = None;

    let mut pos = 0;
    // Tar headers are always 512 bytes in length.
    const HEADER_LEN: usize = 512;
    while pos < input.len() {
        // Consume `HEADER_LEN` bytes and parse them as a `tar::Header`.
        debug_assert_eq!(pos % HEADER_LEN, 0);
        let header_start = pos;
        pos = pos.checked_add(HEADER_LEN)
            .ok_or_else(|| io::Error::other(format!("pos overflow: {pos} + {HEADER_LEN}")))?;
        let header_end = pos;
        let header_bytes = input.get(header_start .. header_end)
            .ok_or_else(|| io::Error::other(format!(
                "not enough bytes for header: end {header_end} >= len {}", input.len())))?;
        // "The end of an archive is marked by at least two consecutive zero-filled records."  We
        // just skip all-zero headers, and stop upon reaching the end of the file.
        if header_bytes.iter().all(|&b| b == 0) {
            continue;
        }
        let header = tar::Header::from_byte_slice(header_bytes);

        let path = header.path()?;

        let size = header.size()?;
        let entry_size = header.entry_size()?;
        if entry_size != size {
            return Err(io::Error::other(format!("sparse files are not supported: \
                size {size} != entry_size {entry_size}, for {path:?}")).into());
        }
        let size = usize::try_from(size)
            .map_err(|_| io::Error::other(format!("size {size} for {path:?} is out of range")))?;
        let data_start = pos;
        let data_end = data_start.checked_add(size)
            .ok_or_else(|| io::Error::other(format!(
                "size overflow for {path:?}: {data_start} + {size}")))?;
        // Entries are padded to a multiple of 512.
        let padded_size = size.checked_next_multiple_of(HEADER_LEN)
            .ok_or_else(|| io::Error::other(format!("size {size} for {path:?} is out of range")))?;
        pos = pos.checked_add(padded_size)
            .ok_or_else(|| io::Error::other(format!("pos overflow: {pos} + {padded_size}")))?;

        let data_bytes = input.get(data_start .. data_end)
            .ok_or_else(|| io::Error::other(format!(
                "not enough bytes for file {path:?}: end {data_end} >= len {}", input.len())))?;

        if path == Path::new("index.cbor") {
            assert!(index.is_none(), "duplicate crate.json in archive?");
            index = Some(serde_cbor::from_slice(data_bytes)?);
        } else if path == Path::new("crate.json") {
            assert!(json_offset.is_none(), "duplicate crate.json in archive?");
            json_offset = Some(data_start);
        }
    }

    let index = index
        .ok_or_else(|| io::Error::other("index.cbor not found in archive"))?;
    let json_offset = json_offset
        .ok_or_else(|| io::Error::other("crate.json not found in archive"))?;

    Ok((index, json_offset))
}


// JSON output modes

pub trait JsonOutput {
    fn emit(&mut self, kind: EntryKind, j: serde_json::Value) -> io::Result<()>;
    fn add_root(&mut self, name: String, is_test: bool) -> io::Result<()>;
}

#[derive(Default)]
pub struct Output {
    /// MIR bodies.  These can come from monomorphized fns, monomorphized constants, and static
    /// initializers.
    pub fns: Vec<serde_json::Value>,
    /// Definitions of all ADTs used in the crate.
    pub adts: Vec<serde_json::Value>,
    /// Declarations of statics, giving their names and types.  The code that initializes the
    /// static appears as a MIR body in `fns` with matching name.
    pub statics: Vec<serde_json::Value>,
    /// Definitions of all trait-object vtables used in the crate.  A vtable is "used" when an
    /// unsizing cast converts a normal pointer into a trait object fat pointer.
    pub vtables: Vec<serde_json::Value>,
    /// All traits defined in the crate.  This gives the name and signature of each trait item,
    /// which is useful for constructing vtable types.
    pub traits: Vec<serde_json::Value>,
    /// Provides the `instance` for each monomorphized function used in the crate that doesn't have
    /// a MIR body.
    pub intrinsics: Vec<serde_json::Value>,
    /// Types that are referenced in this crate.  `ty::Ty` is serialized as a string ID, which is a
    /// key into this table.  This encoding avoids exponential blowup when large types appear
    /// repeatedly within a crate.
    pub tys: Vec<serde_json::Value>,
    /// For each
    /// [lang item](https://doc.rust-lang.org/unstable-book/language-features/lang-items.html),
    /// this gives the lang item identifier (e.g., `$lang/0::Option`) and the
    /// original identifier (e.g., `core/123456::option::Option`). Currently,
    /// this only contains the identifiers for ADT definitions.
    ///
    /// This is of primary benefit for SAW, as SAW users look up ADT names by
    /// providing the original identifier, which SAW can then map back to the
    /// lang item identifier used throughout the rest of the MIR code.
    pub lang_items: Vec<serde_json::Value>,
    /// Entry points for this crate.  We generate definition for all of these
    /// and their dependencies.
    pub roots: Vec<String>,
    /// Subsets of `roots` that corresponds to tests we want to execute.
    /// This might differ from `roots` when we want to translate more than
    /// we need for execution, so that we can report coverage statistics,
    /// for example.
    pub tests: Vec<String>,
}

impl JsonOutput for Output {
    fn emit(&mut self, kind: EntryKind, j: serde_json::Value) -> io::Result<()> {
        match kind {
            EntryKind::Fn => self.fns.push(j),
            EntryKind::Adt => self.adts.push(j),
            EntryKind::Static => self.statics.push(j),
            EntryKind::Vtable => self.vtables.push(j),
            EntryKind::Trait => self.traits.push(j),
            EntryKind::Intrinsic => self.intrinsics.push(j),
            EntryKind::Ty => self.tys.push(j),
            EntryKind::LangItem => self.lang_items.push(j),
        }
        Ok(())
    }

    fn add_root(&mut self, name: String, is_test: bool) -> io::Result<()> {
        if is_test { self.tests.push(name.clone()) }
        self.roots.push(name);
        Ok(())
    }
}


/// Streaming output of MIR entries.  This uses a different output format: instead of an object
/// containing a named tables for each `EntryKind`, the output is a single giant array where each
/// entry is tagged with its `EntryKind`.  This lets us emit it in a streaming fashion, without
/// ever buffering all JSON objects in memory.
pub struct StreamingEmitter<W> {
    /// Internally, `StreamingEmitter` writes the JSON and constructs the `CrateIndex` using an
    /// `Emitter`.  But we use private functions to emit a single entry at a time, rather than
    /// producing an entire crate via `emit_crate`.
    inner: Emitter<W>,
    len: usize,
}

impl<W: Write> StreamingEmitter<W> {
    pub fn new(w: W) -> io::Result<StreamingEmitter<W>> {
        let mut se = StreamingEmitter {
            inner: Emitter::new(w),
            len: 0,
        };
        // Write the opening `[` through the inner `CountWrite` so that the index will contain
        // accurate offsets.
        write!(se.inner.writer, "[")?;
        Ok(se)
    }

    pub fn finish(mut self, extra_data: CrateDependencies) -> io::Result<(W, CrateIndex)> {
        // TODO: expose this through a method on Emitter rather than reaching into its internal
        // state.
        let index = self.inner.state.finish(extra_data);
        write!(self.inner.writer, "]")?;
        Ok((self.inner.writer.w, index))
    }
}

impl<W: Write> JsonOutput for StreamingEmitter<W> {
    fn emit(&mut self, kind: EntryKind, j: serde_json::Value) -> io::Result<()> {
        if self.len > 0 {
            write!(self.inner.writer, ",")?;
        }
        write!(self.inner.writer, r#"{{"kind":"{}","data":"#, kind.name())?;
        self.inner.emit_entry(kind, &j)?;
        write!(self.inner.writer, r#"}}"#)?;
        self.len += 1;
        Ok(())
    }

    fn add_root(&mut self, name: String, is_test: bool) -> io::Result<()> {
        self.inner.add_root(name.into(), is_test);
        Ok(())
    }
}


// Streaming tar-file output.

pub struct MirStream {
    emitter: StreamingEmitter<TarEntryStream<BufWriter<File>>>,
}

impl JsonOutput for MirStream {
    fn emit(&mut self, kind: EntryKind, j: serde_json::Value) -> io::Result<()> {
        self.emitter.emit(kind, j)
    }

    fn add_root(&mut self, name: String, is_test: bool) -> io::Result<()> {
        self.emitter.add_root(name, is_test)
    }
}

fn make_tar_entry(path: &str) -> io::Result<tar::Header> {
    let mut h = tar::Header::new_gnu();
    h.set_path(path)?;
    h.set_mode(0o644);
    h.set_uid(0);
    h.set_gid(0);
    h.set_mtime(0);
    h.set_entry_type(tar::EntryType::Regular);
    Ok(h)
}

pub fn start_streaming(path: &Path) -> io::Result<MirStream> {
    let tar = TarStream::new(BufWriter::new(File::create(path)?));
    let entry = tar.start_entry(make_tar_entry("crate.json")?)?;
    let emitter = StreamingEmitter::new(entry)?;
    Ok(MirStream { emitter })
}

pub fn finish_streaming(ms: MirStream, extra_data: CrateDependencies) -> serde_cbor::Result<()> {
    let (json_entry, index) = ms.emitter.finish(extra_data)?;
    let tar = json_entry.finish_entry()?;
    let mut index_entry = tar.start_entry(make_tar_entry("index.cbor")?)?;
    serde_cbor::to_writer(&mut index_entry, &index)?;
    let tar = index_entry.finish_entry()?;
    let mut w = tar.finish()?;
    w.flush()?;
    Ok(())
}

#[derive(Debug)]
pub struct DependencyError {
    root_hash: UniqueCrateId,
    dependency_hashes: Vec<UniqueCrateId>,
}

impl std::fmt::Display for DependencyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "The crate {} depends on {:#?} which was not provided as an input to the linker", self.root_hash, self.dependency_hashes)
    }
}

impl std::error::Error for DependencyError {}

/// Function that checks if the crate dependencies were provided as inputs to the linker


/*
Note [Excluding proc macro crates]
~~~~~~~~~~~~~~~~~~~~~
(Courtesy of @spernsteiner)

We exclude proc macro crates in the check below because they are not linked into the final artifact.
In general, since proc macro crates are always compiled for the host architecture rather than the target 
architecture (which may be different, even if in practice it's usually the same), 
they can't be linked into target-architecture build outputs (and anyway there's no need, 
since the proc macro code only runs at compile time).


For example, suppose you have crate foo that depends on my_proc_macros and bar (a normal, non-proc-macro crate).  
If you're on an amd64 machine and cross-compiling for wasm, then Cargo will build bar for wasm so it can be
linked into the final wasm output, but it will build my_proc_macros for amd64 so the code from that crate 
can be loaded and run while compiling foo (which happens on your amd64 build machine). 
*/
pub fn check_dependencies(crate_indices: &[CrateIndex]) -> Result<(), DependencyError> {
    let mut linker_inputs: HashSet<UniqueCrateId>  = HashSet::new();
    for index in crate_indices {
        linker_inputs.insert(index.root_hash());
    }
    for index in crate_indices {
        let diff: Vec<UniqueCrateId> = index.dep_hashes().difference(&linker_inputs).map(|hash|hash.clone()).collect();
        if diff.len() != 0 {
            return Err(DependencyError{root_hash: index.root_hash(), dependency_hashes: diff});
        }
    }
    return Ok(());
}


impl From<DependencyError> for serde_cbor::Error {
    fn from(error: DependencyError) -> Self {
        ser::Error::custom(error.to_string())
    }
}

#[derive(Debug)]
pub struct EmptyCrateDependenciesError;

impl std::fmt::Display for EmptyCrateDependenciesError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "The CrateDependencies struct that uniquely identifies a crate and its independencies was not provided!")
    }
}

impl std::error::Error for EmptyCrateDependenciesError {}

impl From<EmptyCrateDependenciesError> for serde_cbor::Error {
    fn from(error: EmptyCrateDependenciesError) -> Self {
        ser::Error::custom(error.to_string())
    }
}
