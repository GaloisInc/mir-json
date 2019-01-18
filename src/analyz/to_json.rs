use rustc::hir::def_id::DefId;
use rustc::mir::Mir;
use rustc_driver::driver::CompileState;
use syntax::symbol::Symbol;
use serde_json;
use std::collections::BTreeMap;
use std::collections::HashSet;

pub struct MirState<'a, 'tcx> {
    pub mir: Option<&'a Mir<'a>>,
    pub used_types: &'a mut HashSet<DefId>,
    pub state: &'a CompileState<'a, 'tcx>
}

pub trait ToJson {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value;
}

impl ToJson for String {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        json!(self)
    }
}

impl ToJson for Symbol {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        json!(*self.as_str())
    }
}

impl<T> ToJson for Option<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &Some(ref i) => i.to_json(mir),
            &None => serde_json::Value::Null,
        }
    }
}

impl<K, V> ToJson for BTreeMap<K, V>
    where
    K: ToJson,
    V: ToJson,
{
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
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
        impl ToJson for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson for $n {
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
        impl ToJson for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson for $n {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}

};
}

impl<A, B> ToJson for (A, B)
where
    A: ToJson,
    B: ToJson,
{
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        let &(ref a, ref b) = self;
        json!(vec![a.to_json(mir), b.to_json(mir)])
    }
}

impl<T> ToJson for Vec<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}
