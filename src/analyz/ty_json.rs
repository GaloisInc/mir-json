use rustc::hir;
use rustc::mir;
use rustc::mir::interpret;
use rustc::ty;
use syntax::ast;
use serde_json;
use std::fmt::Write as FmtWrite;

use analyz::to_json::*;

impl<T> ToJson for ty::List<T>
    where
    T: ToJson,
{
    fn to_json<'a, 'tcx: 'a>(&self, mir: &mut MirState<'a, 'tcx>) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}

basic_json_enum_impl!(ast::FloatTy);
basic_json_enum_impl!(ast::IntTy);
basic_json_enum_impl!(ast::UintTy);
basic_json_enum_impl!(hir::Mutability);
basic_json_enum_impl!(hir::def::CtorKind);
basic_json_enum_impl!(mir::Mutability);
basic_json_enum_impl!(mir::CastKind);

impl ToJson for mir::BorrowKind {
    fn to_json<'a, 'tcx: 'a>(&self, _mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::BorrowKind::Shared => json!("Shared"),
            &mir::BorrowKind::Shallow => json!("Shallow"),
            &mir::BorrowKind::Unique => json!("Unique"),
            &mir::BorrowKind::Mut{..} => json!("Mut"),
        }
    }
}

impl ToJson for ty::VariantDiscr {
    fn to_json<'a, 'tcx: 'a>(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &ty::VariantDiscr::Relative(i) => {
                json!({"kind": "Relative", "index" : json!(i)})
            }
            &ty::VariantDiscr::Explicit(n) => {
                json!({"kind": "Explicit", "name" : n.to_json(mir)})
            }
        }
    }
}

impl ToJson for hir::def_id::DefId {
    fn to_json<'a, 'tcx: 'a>(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(ty::tls::with(|tx| {
            let defpath = tx.def_path(*self);
            defpath.to_string_no_crate()
        }))
    }
}

// For type _references_. To translate ADT defintions, do it explicitly.
impl<'b> ToJson for ty::Ty<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, mir: &mut MirState) -> serde_json::Value {
        match &self.sty {
            &ty::TyKind::Bool => {
                json!({"kind": "Bool"})
            }
            &ty::TyKind::Char => {
                json!({"kind": "Char"})
            }
            &ty::TyKind::Int(ref t) => {
                json!({"kind": "Int", "intkind": t.to_json(mir)})
            }
            &ty::TyKind::Uint(ref t) => {
                json!({"kind": "Uint", "uintkind": t.to_json(mir)})
            }
            &ty::TyKind::Tuple(ref sl) => {
                json!({"kind": "Tuple", "tys": sl.to_json(mir)})
            }
            &ty::TyKind::Slice(ref f) => {
                json!({"kind": "Slice", "ty": f.to_json(mir)})
            }
            &ty::TyKind::Str => {
                json!({"kind": "Str"})
            }
            &ty::TyKind::Float(ref sz) => {
                json!({"kind": "Float", "size": sz.to_json(mir)})
            }
            &ty::TyKind::Array(ref t, ref size) => {
                json!({"kind": "Array", "ty": t.to_json(mir), "size": size.to_json(mir)})
            }
            &ty::TyKind::Ref(ref _region, ref ty, ref mtbl) => {
                json!({
                    "kind": "Ref",
                    "ty": ty.to_json(mir),
                    "mutability": mtbl.to_json(mir)
                })
            }
            &ty::TyKind::RawPtr(ref tm) => {
                json!({
                    "kind": "RawPtr",
                    "ty": tm.ty.to_json(mir),
                    "mutability": tm.mutbl.to_json(mir)
                })
            }
            &ty::TyKind::Adt(ref adtdef, ref substs) => {
                let did = adtdef.did;
                mir.used_types.insert(did);
                json!({
                    "kind": "Adt",
                    "name": defid_str(&did),
                    "substs": substs.to_json(mir)
                })
            }
            &ty::TyKind::FnDef(defid, ref substs) => {
                json!({
                    "kind": "FnDef",
                    "defid": defid.to_json(mir),
                    "substs": substs.to_json(mir)
                })
            }
            &ty::TyKind::Param(ref p) =>
                json!({"kind": "Param", "param": p.to_json(mir)}),
            &ty::TyKind::Closure(ref defid, ref closuresubsts) => {
                json!({
                    "kind": "Closure",
                    "defid": defid.to_json(mir),
                    "closuresubsts": closuresubsts.substs.to_json(mir)
                })
            }
            &ty::TyKind::Dynamic(ref bs, _) => {
                let did = bs.principal().skip_binder().def_id;
                json!({
                    "kind": "Dynamic",
                    "data": did.to_json(mir)
                    /*, "region": r.to_json(mir)*/
                })
            }
            &ty::TyKind::Projection(ref pty) => {
                json!({
                    "kind": "Projection",
                    "substs": pty.substs.to_json(mir),
                    "defid": pty.item_def_id.to_json(mir)
                })
            }
            &ty::TyKind::UnnormalizedProjection(ref pty) => {
                json!({
                    "kind": "UnnormalizedProjection",
                    "substs": pty.substs.to_json(mir),
                    "defid": pty.item_def_id.to_json(mir)
                })
            }
            &ty::TyKind::FnPtr(ref sig) => {
                json!({"kind": "FnPtr", "signature": sig.to_json(mir)})
            }
            &ty::TyKind::Never => {
                json!({"kind": "Never"})
            }
            &ty::TyKind::Error => {
                json!({"kind": "Error"})
            }
            &ty::TyKind::Infer(_) => {
                // TODO
                json!({"kind": "Infer"})
            }
            /*
            &ty::TyKind::Bound(_, _) => {
                // TODO
                json!({"kind": "Bound"})
            }
            */
            &ty::TyKind::Foreign(_) => {
                // TODO
                json!({"kind": "Foreign"})
            }
            &ty::TyKind::Generator(_, _, _) => {
                // TODO
                json!({"kind": "Generator"})
            }
            &ty::TyKind::GeneratorWitness(_) => {
                // TODO
                json!({"kind": "GeneratorWitness"})
            }
            &ty::TyKind::Opaque(_, _) => {
                // TODO
                json!({"kind": "Opaque"})
            }
        }
    }
}

impl ToJson for ty::ParamTy {
    fn to_json<'a, 'tcx: 'a>(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(self.idx)
    }
}

impl<'b> ToJson for ty::PolyFnSig<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        // Note: I don't think we need binders in MIR, but we can change
        // this if we do.
        self.skip_binder().to_json(ms)
    }
}

impl<'b> ToJson for ty::FnSig<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        let input_jsons : Vec<serde_json::Value> =
            self.inputs().iter().map(|i| i.to_json(ms)).collect();
        json!({
            "inputs": input_jsons,
            "output": self.output().to_json(ms)
        })
    }
}

impl<'b> ToJson for ty::PolyTraitPredicate<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        let tref = self.skip_binder().trait_ref;
        json!({
            "trait":  tref.def_id.to_json(ms),
            "substs":  tref.substs.to_json(ms)
        })
    }
}

impl<'b> ToJson for ty::ProjectionPredicate<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        json!({
            "projection_ty": self.projection_ty.to_json(ms),
            "ty": self.ty.to_json(ms)
        })
    }
}

impl<'b> ToJson for ty::ProjectionTy<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        json!({
            "substs": self.substs.to_json(ms),
            "item_def_id": self.item_def_id.to_json(ms)
        })
    }
}

impl<'b> ToJson for ty::Predicate<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        match self {
            &ty::Predicate::Trait(ref ptp) => {
                json!({
                    "trait_pred": ptp.to_json(ms)
                })
            }
            &ty::Predicate::Projection(ref ppp) => {
                json!({
                    "trait_proj": ppp.skip_binder().to_json(ms)
                })
            }
            _ => {
                json!("unknown_pred")
            }
        }
    }
}

impl<'b> ToJson for ty::GenericPredicates<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        let preds : Vec<serde_json::Value> =
            self.predicates.iter().map(|p| p.0.to_json(ms)).collect();
        json!({ "predicates": preds })
    }
}

impl ToJson for ty::GenericParamDef {
    fn to_json<'a, 'tcx: 'a>(&self, _ms: &mut MirState) -> serde_json::Value {
        json!({
            "param_def": *(self.name.as_str())
        }) // TODO
    }
}

impl ToJson for ty::Generics {
    fn to_json<'a, 'tcx: 'a>(&self, ms: &mut MirState) -> serde_json::Value {
        let params : Vec<serde_json::Value> =
          self.params.iter().map(|p| p.to_json(ms)).collect();
        json!({
            "params": params
        }) // TODO
    }
}

pub fn assoc_item_json<'a, 'tcx: 'a>(
    ms: &mut MirState<'a, 'tcx>,
    tcx: &ty::TyCtxt<'a, 'tcx, 'tcx>,
    item: &ty::AssociatedItem
) -> serde_json::Value {
    let did = item.def_id;
    match item.kind {
        ty::AssociatedKind::Const => {
            json!({
                "kind": "Const",
                "name": did.to_json(ms),
                "type": tcx.type_of(did).to_json(ms)
            })
        }
        ty::AssociatedKind::Method => {
            let sig = tcx.fn_sig(did);
            json!({
                "kind": "Method",
                "name": did.to_json(ms),
                "signature": sig.to_json(ms)
            })
        }
        ty::AssociatedKind::Type => {
            json!({"kind": "Type", "name": did.to_json(ms)})
        }
        ty::AssociatedKind::Existential => {
            json!({"kind": "Existential"})
        }
    }
}

pub fn defid_str(d: &hir::def_id::DefId) -> String {
    ty::tls::with(|tx| {
        let defpath = tx.def_path(*d);
        defpath.to_string_no_crate()
    })
}

pub fn defid_ty(d: &hir::def_id::DefId, mir: &mut MirState) -> serde_json::Value {
    ty::tls::with(|tx| tx.type_of(*d).to_json(mir))
}

pub trait ToJsonAg {
    fn tojson<'a, 'tcx: 'a>(
        &self,
        mir: &mut MirState,
        substs: &ty::subst::Substs,
    ) -> serde_json::Value;
}

impl<'b> ToJson for ty::subst::Kind<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, mir: &mut MirState) -> serde_json::Value {
        match self.unpack() {
            ty::subst::UnpackedKind::Type(ref ty) => ty.to_json(mir),
            ty::subst::UnpackedKind::Lifetime(_) => json!({"kind": "Lifetime"})
        }
    }
}

impl<'b> ToJson for ty::Const<'b> {
    fn to_json<'a, 'tcx: 'a>(&self, mir: &mut MirState) -> serde_json::Value {
        let mut s = String::new();
        match &self.val {
            &interpret::ConstValue::Unevaluated(def_id, ref substs) => {
                /*
                let tcx = mir.state.tcx.unwrap();
                let param_env = ty::ParamEnv::reveal_all();
                let instance = ty::Instance::resolve(tcx, param_env, def_id, substs).unwrap();
                let cid = interpret::GlobalId {
                    instance,
                    promoted: None,
                };
                tcx.const_eval(param_env.and(cid)).unwrap().clone();
                */
                // TODO: the following should use the result of const_eval instead of self.
                mir::fmt_const_val(&mut s, &self);
            }
            _ => {
                mir::fmt_const_val(&mut s, &self);
            }
        }
        json!({
            "kind": "Const",
            "ty": self.ty.to_json(mir),
            "val": s
        })
    }
}

impl<T> ToJsonAg for Vec<T>
where
    T: ToJsonAg,
{
    fn tojson<'a, 'tcx: 'a>(&self, mir: &mut MirState, substs: &ty::subst::Substs) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.tojson(mir, substs));
        }
        json!(j)
    }
}

pub fn is_adt_ak(ak: &mir::AggregateKind) -> bool {
    match ak {
        &mir::AggregateKind::Adt(_, _, _, _, _) => true,
        _ => false,
    }
}

impl ToJsonAg for ty::AdtDef {
    fn tojson<'a, 'tcx: 'a>(&self, mir: &mut MirState, substs: &ty::subst::Substs) -> serde_json::Value {
        json!({
            "name": defid_str(&self.did),
            "variants": self.variants.tojson(mir, substs)
        })
    }
}

impl ToJsonAg for ty::VariantDef {
    fn tojson<'a, 'tcx: 'a>(&self, mir: &mut MirState, substs: &ty::subst::Substs) -> serde_json::Value {
        json!({
            "name": defid_str(&self.did),
            "discr": self.discr.to_json(mir),
            "fields": self.fields.tojson(mir, substs),
            "ctor_kind": self.ctor_kind.to_json(mir)
        })
    }
}

impl ToJsonAg for ty::FieldDef {
    fn tojson<'a, 'tcx: 'a>(
        &self,
        mir: &mut MirState,
        substs: &ty::subst::Substs,
    ) -> serde_json::Value {
        json!({
            "name": defid_str(&self.did),
            "ty": defid_ty(&self.did, mir),
            "substs": substs.to_json(mir)
        })
    }
}

pub fn handle_adt_ag(
    mir: &mut MirState,
    ak: &mir::AggregateKind,
    opv: &Vec<mir::Operand>,
) -> serde_json::Value {
    match ak {
        &mir::AggregateKind::Adt(ref adt, variant, substs, _, _) => {
            json!({
                "adt": adt.tojson(mir, substs),
                "variant": variant, //.to_json(mir),
                "ops": opv.to_json(mir)
            })
        }
        _ => unreachable!("bad"),
    }
}
