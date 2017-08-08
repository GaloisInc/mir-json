use rustc::ty::{self, TyCtxt};
use rustc::mir::{self, Mir}; 
use rustc::mir::transform::{MirSource};
use rustc::hir::{self, def_id};
use rustc_data_structures::indexed_vec::Idx;
use rustc::middle;
use rustc::hir::def_id::DefId;
use syntax::{self,ast};
use rustc_driver::driver::{CompileState };
use rustc_const_math;
use std::fmt::Write as FmtWrite;
use serde_json;
use analyz::ToJson;
// custom type overrides
//
//

pub fn defid_str (d : &hir::def_id::DefId) -> String {
    ty::tls::with(|tx| {
        let defpath = tx.def_path(*d);
        defpath.to_string(tx)
    })
}
            

pub fn is_adt_ak (ak : &mir::AggregateKind) -> bool {
    match ak {
        &mir::AggregateKind::Adt(a, b, c, _) => true,
        _ => false
    }
}


pub fn handle_adt (mir : &Mir, adt : &ty::AdtDef, substs : &ty::subst::Substs) -> serde_json::Value {
    if let Some(v) = custom_adt_ser(mir, adt, substs) {
        v
    }
    else {
        regular_adt_ser (adt, substs)
    }
}

pub fn is_custom_adt (adt : &ty::AdtDef) -> bool {
    match &defid_str(&adt.did) as &str {
        "core/ebcf64d::ops[0]::range[0]::Range[0]" => true,
        "alloc/39550c7::boxed[0]::Box[0]" => true,
        "alloc/39550c7::vec[0]::Vec[0]" => true,
        _ => false
    }
}

pub fn custom_adt_ser (mir : &Mir, adt : &ty::AdtDef, substs : &ty::subst::Substs) -> Option<serde_json::Value> {
    match &defid_str(&adt.did) as &str {
        "core/ebcf64d::ops[0]::range[0]::Range[0]" => Some(json!({"kind": "custom", "data": {"kind": "Range", "range_ty": substs[0].as_type().unwrap().to_json(mir)}})),
        "alloc/39550c7::boxed[0]::Box[0]" => Some(json!({"kind": "custom", "data": {"kind": "Box", "box_ty": substs[0].as_type().unwrap().to_json(mir)}})),
        "alloc/39550c7::vec[0]::Vec[0]" => Some(json!({"kind": "custom", "data": {"kind": "Vec", "vec_ty": substs[0].as_type().unwrap().to_json(mir)}})),
        _ => None
    }
}

pub fn regular_adt_ser (adt : &ty::AdtDef, substs : &ty::subst::Substs) -> serde_json::Value {
    panic!(format!("regular: {:?}", adt.variants))
}

pub fn handle_adt_ag_ (mir : &Mir, adt : &ty::AdtDef, num_variants : usize, substs : &ty::subst::Substs, opv : &Vec<mir::Operand>) -> serde_json::Value {
    match &defid_str(&adt.did) as &str {
        "core/ebcf64d::ops[0]::range[0]::Range[0]" => {
            let range_ty = substs[0].as_type().unwrap();
            json!({"kind": "custom", "data": {
                "kind": "range",
                "range_ty": range_ty.to_json(mir),
                "f1": opv[0].to_json(mir),
                "f2": opv[1].to_json(mir)}})
        },
        _ => panic!("unimplemented")
    }
}

pub fn handle_adt_ag (mir: &Mir, ak : &mir::AggregateKind, opv : &Vec<mir::Operand>) -> serde_json::Value {
    match ak {
        &mir::AggregateKind::Adt(a, b, c, _) => handle_adt_ag_(mir, a,b,c, opv),
        _ => unreachable!("bad")
    }
}
