use rustc::ty::{self, TyCtxt};
use rustc::mir::{self, Mir};
use rustc::mir::transform::MirSource;
use rustc::hir::{self, def_id};
use rustc_data_structures::indexed_vec::Idx;
use rustc::middle;
use rustc::hir::def_id::DefId;
use syntax::{self, ast};
use rustc_driver::driver::CompileState;
use rustc_const_math;
use std::fmt::Write as FmtWrite;
use rustc::ty::subst::Subst;
use serde_json;
use analyz::ToJson;

trait ToJsonAg {
    fn tojson<'a, 'tcx>(
        &self,
        mir: &'a Mir<'a>,
        substs: &'tcx ty::subst::Substs<'tcx>,
    ) -> serde_json::Value;
}


impl<'a> ToJson for ty::subst::Kind<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        self.as_type().to_json(mir)
    }
}

impl<T> ToJsonAg for Vec<T>
where
    T: ToJsonAg,
{
    fn tojson(&self, mir: &Mir, substs: &ty::subst::Substs) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.tojson(mir, substs));
        }
        json!(j)
    }
}

pub fn is_adt_ak(ak: &mir::AggregateKind) -> bool {
    match ak {
        &mir::AggregateKind::Adt(a, b, c, _) => true,
        _ => false,
    }
}

pub fn defid_str(d: &hir::def_id::DefId) -> String {
    ty::tls::with(|tx| {
        let defpath = tx.def_path(*d);
        defpath.to_string(tx)
    })
}

pub fn defid_ty(d: &hir::def_id::DefId, mir: &Mir) -> serde_json::Value {
    ty::tls::with(|tx| tx.type_of(*d).to_json(mir))
}


impl ToJsonAg for ty::AdtDef {
    fn tojson(&self, mir: &Mir, substs: &ty::subst::Substs) -> serde_json::Value {
        json!({"name": defid_str(&self.did), "variants": self.variants.tojson(mir, substs)})
    }
}

impl ToJsonAg for ty::VariantDef {
    fn tojson(&self, mir: &Mir, substs: &ty::subst::Substs) -> serde_json::Value {
        json!({"name": defid_str(&self.did), "discr": self.discr.to_json(mir), "fields": self.fields.tojson(mir, substs), "ctor_kind": self.ctor_kind.to_json(mir)})
    }
}

impl ToJsonAg for ty::FieldDef {
    fn tojson<'a, 'tcx>(
        &self,
        mir: &Mir<'a>,
        substs: &'tcx ty::subst::Substs<'tcx>,
    ) -> serde_json::Value {
        json!({"name": defid_str(&self.did), "ty": defid_ty(&self.did, mir), "substs": substs.to_json(mir)  })
    }
}



impl ToJson for hir::def::CtorKind {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &hir::def::CtorKind::Fn => json!("fn"),
            &hir::def::CtorKind::Const => json!("const"),
            &hir::def::CtorKind::Fictive => json!("fictive"),
        }
    }
}


impl ToJson for ty::VariantDiscr {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &ty::VariantDiscr::Relative(i) => json!(i),
            _ => panic!("explicit variant"),
        }
    }
}

pub fn is_custom(adt: &ty::AdtDef) -> bool {
    match &defid_str(&adt.did) as &str {
        "alloc/39550c7::vec[0]::IntoIter[0]" => true,
        "alloc/39550c7::boxed[0]::Box[0]" => true,
        "alloc/39550c7::vec[0]::Vec[0]" => true,
        "core/ebcf64d::iter[0]::Map[0]" => true,
        _ => false,
    }
}


pub fn handle_adt_custom(
    mir: &Mir,
    adt: &ty::AdtDef,
    substs: &ty::subst::Substs,
) -> serde_json::Value {

    match &defid_str(&adt.did) as &str {
        "alloc/39550c7::boxed[0]::Box[0]" => {
            json!({"kind": "Box", "box_ty": substs[0].as_type().unwrap().to_json(mir)})
        }

        "alloc/39550c7::vec[0]::Vec[0]" => {
            json!({"kind": "Vec", "vec_ty": substs[0].as_type().unwrap().to_json(mir)})
        }
        "alloc/39550c7::vec[0]::IntoIter[0]" => {
            json!({"kind": "Iter", "iter_ty": substs[0].as_type().unwrap().to_json(mir)})
        }
        "core/ebcf64d::iter[0]::Map[0]" => {
            // map is the same as its embedded iter
            let v1 = substs[0].as_type().unwrap().to_json(mir);
            let v = v1.get("data").unwrap();
            v.clone()
        }

        _ => panic!("bad custom adt?"),
    }

}

pub fn handle_adt(mir: &Mir, adt: &ty::AdtDef, substs: &ty::subst::Substs) -> serde_json::Value {
    if is_custom(adt) {
        handle_adt_custom(mir, adt, substs)
    } else {
        adt.tojson(mir, substs)
    }
}


pub fn handle_adt_ag_custom(
    mir: &Mir,
    adt: &ty::AdtDef,
    substs: &ty::subst::Substs,
    variant: usize,
    opv: &Vec<mir::Operand>,
) -> serde_json::Value {
    panic!("unimpl")
}

pub fn handle_adt_ag(
    mir: &Mir,
    ak: &mir::AggregateKind,
    opv: &Vec<mir::Operand>,
) -> serde_json::Value {
    match ak {
        &mir::AggregateKind::Adt(ref adt, variant, substs, _) => {
            if is_custom(adt) {
                handle_adt_ag_custom(mir, adt, substs, variant, opv)
            } else {
                json!({"adt": adt.tojson(mir, substs), "variant": variant, "ops": opv.to_json(mir)})
            }
        }
        _ => unreachable!("bad"),
    }
}
