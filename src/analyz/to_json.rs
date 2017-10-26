use rustc::mir::Mir;
use serde_json;

pub trait ToJson {
    fn to_json(&self, mir: &Mir) -> serde_json::Value;
}

impl ToJson for String {
    fn to_json(&self, _: &Mir) -> serde_json::Value {
        json!(self)
    }
}

impl<T> ToJson for Option<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &Some(ref i) => i.to_json(mir),
            &None => json!("null"),
        }
    }
}

#[macro_export]
macro_rules! basic_json_impl {
    ($n : path) => {
        impl ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
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
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
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
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        let &(ref a, ref b) = self;
        json!(vec![a.to_json(mir), b.to_json(mir)])
    }
}

impl<T> ToJson for Vec<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}
