use rustc::hir::def_id::DefId;
use rustc::mir::Body;
use rustc::session::Session;
use rustc::ty::{self, TyCtxt};
use rustc_interface::interface::Compiler;
use syntax::symbol::Symbol;
use serde_json;
use std::collections::BTreeMap;
use std::collections::{HashMap, HashSet, hash_map};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::mem;

pub struct CompileState<'a, 'tcx> {
    pub session: &'a Session,
    pub tcx: TyCtxt<'tcx>,
}

#[derive(Clone, Debug)]
pub struct UsedSet<T: Hash+Eq> {
    cur: HashSet<T>,
    new: HashSet<T>,
}

impl<T: Hash+Eq> Default for UsedSet<T> {
    fn default() -> Self {
        UsedSet {
            cur: HashSet::new(),
            new: HashSet::new(),
        }
    }
}

impl<T: Hash+Eq+Clone> UsedSet<T> {
    pub fn insert(&mut self, x: T) {
        if self.cur.insert(x.clone()) {
            // `x` was not in `cur`
            self.new.insert(x);
        }
    }

    pub fn take_new(&mut self) -> HashSet<T> {
        mem::replace(&mut self.new, HashSet::new())
    }

    pub fn has_new(&self) -> bool {
        self.new.len() > 0
    }

    pub fn count_new(&self) -> usize {
        self.new.len()
    }
}

impl<T: Hash+Eq> Deref for UsedSet<T> {
    type Target = HashSet<T>;
    fn deref(&self) -> &HashSet<T> {
        &self.cur
    }
}

#[derive(Default)]
pub struct Used<'tcx> {
    pub types: UsedSet<DefId>,
    pub vtables: UsedSet<ty::PolyTraitRef<'tcx>>,
    pub instances: UsedSet<ty::Instance<'tcx>>,
}

impl<'tcx> Used<'tcx> {
    pub fn has_new(&self) -> bool {
        let Used { ref types, ref vtables, ref instances } = *self;
        types.has_new() ||
        vtables.has_new() ||
        instances.has_new()
    }

    pub fn count_new(&self) -> usize {
        let Used { ref types, ref vtables, ref instances } = *self;
        types.count_new() +
        vtables.count_new() +
        instances.count_new()
    }
}

#[derive(Default, Debug)]
pub struct TyIntern<'tcx> {
    map: HashMap<ty::Ty<'tcx>, String>,
    /// Types that are newly referenced since the last `take_new_types()`.
    new_vals: Vec<serde_json::Value>,
}

/// Info for describing a type.  The `String` indicates (at minimum) the `TyKind`, and the `bool`
/// is `true` if a hash of the type should be included when forming the type's unique ID.
fn ty_desc(ty: ty::Ty) -> (String, bool) {
    let kind_str = match ty.sty {
        // Special case: primitive types print as themselves and don't require a hash.
        ty::TyKind::Bool |
        ty::TyKind::Char |
        ty::TyKind::Int(_) |
        ty::TyKind::Uint(_) |
        ty::TyKind::Float(_) |
        ty::TyKind::Str => return (format!("{:?}", ty), false),

        ty::TyKind::Never |
        ty::TyKind::Error => return (format!("{:?}", ty.sty), false),

        ty::TyKind::Adt(..) => "Adt",
        ty::TyKind::Foreign(..) => "Foreign",
        ty::TyKind::Array(..) => "Array",
        ty::TyKind::Slice(..) => "Slice",
        ty::TyKind::RawPtr(..) => "RawPtr",
        ty::TyKind::Ref(..) => "Ref",
        ty::TyKind::FnDef(..) => "FnDef",
        ty::TyKind::FnPtr(..) => "FnPtr",
        ty::TyKind::Dynamic(..) => "Dynamic",
        ty::TyKind::Closure(..) => "Closure",
        ty::TyKind::Generator(..) => "Generator",
        ty::TyKind::GeneratorWitness(..) => "GeneratorWitness",
        ty::TyKind::Tuple(..) => "Tuple",
        ty::TyKind::Projection(..) => "Projection",
        ty::TyKind::UnnormalizedProjection(..) => "UnnormalizedProjection",
        ty::TyKind::Opaque(..) => "Opaque",
        ty::TyKind::Param(..) => "Param",
        ty::TyKind::Bound(..) => "Bound",
        ty::TyKind::Placeholder(..) => "Placeholder",
        ty::TyKind::Infer(..) => "Infer",
    };
    (kind_str.to_owned(), true)
}

fn ty_unique_id(ty: ty::Ty, j: &serde_json::Value) -> String {
    let (kind_str, needs_hash) = ty_desc(ty);
    if needs_hash {
        let mut h = hash_map::DefaultHasher::new();
        serde_json::to_string(&j).unwrap().hash(&mut h);
        let hash_val = h.finish();
        format!("ty::{}::{:016x}", kind_str, hash_val)
    } else {
        format!("ty::{}", kind_str)
    }
}

impl<'tcx> TyIntern<'tcx> {
    pub fn get(&self, ty: ty::Ty<'tcx>) -> Option<&str> {
        self.map.get(&ty).map(|x| x as &str)
    }

    pub fn insert(&mut self, ty: ty::Ty<'tcx>, j: serde_json::Value) -> String {
        let id = ty_unique_id(ty, &j);
        self.new_vals.push(json!({
            "name": &id,
            "ty": j,
        }));
        let old = self.map.insert(ty, id.clone());
        assert!(old.is_none(), "duplicate insert for type {:?}", ty);
        id
    }

    pub fn take_new_types(&mut self) -> Vec<serde_json::Value> {
        mem::replace(&mut self.new_vals, Vec::new())
    }
}

pub struct MirState<'a, 'tcx : 'a> {
    pub mir: Option<&'tcx Body<'tcx>>,
    pub used: &'a mut Used<'tcx>,
    pub state: &'a CompileState<'a, 'tcx>,
    pub tys: &'a mut TyIntern<'tcx>,
}

/// Trait for converting MIR elements to JSON.
///
/// The `'tcx` parameter allows writing impls like `ToJson<'tcx> for Ty<'tcx>`, where the lifetime
/// parameter on `Self` is known to match the lifetime of `mir.state.tcx`.  This enables passing
/// `self` (or its fields) to some `TyCtxt` methods that would otherwise be unusable.
pub trait ToJson<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value;
}

impl ToJson<'_> for String {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        json!(self)
    }
}

impl ToJson<'_> for Symbol {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        json!(*self.as_str())
    }
}

impl<'tcx, T> ToJson<'tcx> for Option<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &Some(ref i) => i.to_json(mir),
            &None => serde_json::Value::Null,
        }
    }
}

impl<'tcx, T> ToJson<'tcx> for Box<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        <T as ToJson>::to_json(self, mir)
    }
}

impl<'tcx, K, V> ToJson<'tcx> for BTreeMap<K, V>
    where
    K: ToJson<'tcx>,
    V: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut jsons = Vec::new();
        for (k, v) in self.iter() {
            jsons.push(json!({"name": k.to_json(mir), "val": v.to_json(mir)}))
        }
        serde_json::Value::Array(jsons)
    }
}

#[macro_export]
macro_rules! basic_json_impl {
    ($n : path) => {
        impl ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}

};
}

#[macro_export]
macro_rules! basic_json_enum_impl {
    ($n : path) => {
        impl ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson<'_> for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}

};
}

impl<'tcx, A, B> ToJson<'tcx> for (A, B)
where
    A: ToJson<'tcx>,
    B: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let &(ref a, ref b) = self;
        json!(vec![a.to_json(mir), b.to_json(mir)])
    }
}

impl<'tcx, T> ToJson<'tcx> for Vec<T>
where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}
