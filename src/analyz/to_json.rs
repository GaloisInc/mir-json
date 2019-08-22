use rustc::hir::def_id::DefId;
use rustc::mir::Body;
use rustc::session::Session;
use rustc::ty::{self, TyCtxt};
use rustc_interface::interface::Compiler;
use syntax::symbol::Symbol;
use serde_json;
use std::collections::BTreeMap;
use std::collections::HashSet;

pub struct CompileState<'a, 'tcx> {
    pub session: &'a Session,
    pub tcx: TyCtxt<'tcx>,
}

#[derive(Default)]
pub struct Used<'tcx> {
    pub types: HashSet<DefId>,
    pub vtables: HashSet<ty::PolyTraitRef<'tcx>>,
}

pub struct MirState<'a, 'tcx : 'a> {
    pub mir: Option<&'tcx Body<'tcx>>,
    pub used: &'a mut Used<'tcx>,
    pub state: &'a CompileState<'a, 'tcx>,
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
