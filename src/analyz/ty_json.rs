use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_index::vec::{IndexVec, Idx};
use rustc_middle::mir;
use rustc_const_eval::interpret;
use rustc_const_eval::const_eval::CheckAlignment;
use rustc_middle::ty;
use rustc_middle::ty::{TyCtxt, TypeFoldable, TypeVisitable};
use rustc_query_system::ich::StableHashingContext;
use rustc_target::spec::abi;
use rustc_target::abi::Align;
use rustc_ast::ast;
use rustc_span::DUMMY_SP;
use serde_json;
use std::fmt::Write as FmtWrite;
use std::usize;

use analyz::to_json::*;

impl<'tcx, T> ToJson<'tcx> for ty::List<T>
    where
    T: ToJson<'tcx>,
{
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self.iter() {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}

basic_json_enum_impl!(ty::FloatTy);
basic_json_enum_impl!(ty::IntTy);
basic_json_enum_impl!(ty::UintTy);
basic_json_enum_impl!(hir::Mutability);
basic_json_enum_impl!(hir::def::CtorKind);
basic_json_enum_impl!(mir::CastKind);
basic_json_enum_impl!(abi::Abi);

impl ToJson<'_> for mir::BorrowKind {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::BorrowKind::Shared => json!("Shared"),
            &mir::BorrowKind::Shallow => json!("Shallow"),
            &mir::BorrowKind::Unique => json!("Unique"),
            &mir::BorrowKind::Mut{..} => json!("Mut"),
        }
    }
}

impl ToJson<'_> for ty::VariantDiscr {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &ty::VariantDiscr::Relative(i) => {
                json!({"kind": "Relative", "index" : json!(i)})
            }
            &ty::VariantDiscr::Explicit(def_id) => {
                json!({
                    "kind": "Explicit",
                    "name" : get_fn_def_name(mir, def_id, ty::List::empty()),
                })
            }
        }
    }
}

pub fn def_id_str(tcx: TyCtxt, def_id: hir::def_id::DefId) -> String {
    // Based on rustc/ty/context.rs.html TyCtxt::def_path_debug_str
    let crate_name = tcx.crate_name(def_id.krate);
    let disambig = tcx.crate_hash(def_id.krate);
    let defpath = tcx.def_path(def_id);
    format!(
        "{}/{}{}",
        crate_name,
        &disambig.to_string()[..8],
        defpath.to_string_no_crate_verbose(),
    )
}

pub fn ext_def_id_str<'tcx, T>(
    tcx: TyCtxt<'tcx>,
    def_id: hir::def_id::DefId,
    prefix: &str,
    extra: T,
) -> String
where T: for<'a> HashStable<StableHashingContext<'a>> {
    let base = def_id_str(tcx, def_id);

    // Based on librustc_codegen_utils/symbol_names/legacy.rs get_symbol_hash
    let hash: u64 = tcx.with_stable_hashing_context(|mut hcx| {
        let mut hasher = StableHasher::new();
        extra.hash_stable(&mut hcx, &mut hasher);
        hasher.finish()
    });
    format!("{}::{}{:016x}[0]", base, prefix, hash)
}

pub fn adt_inst_id_str<'tcx>(
    tcx: TyCtxt<'tcx>,
    ai: AdtInst<'tcx>,
) -> String {
    // Erase all early-bound regions.
    let substs = tcx.erase_regions(ai.substs);
    ext_def_id_str(tcx, ai.def_id(), "_adt", substs)
}

pub fn inst_id_str<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: ty::Instance<'tcx>,
) -> String {
    let substs = tcx.normalize_erasing_regions(
        ty::ParamEnv::reveal_all(),
        inst.substs,
    );
    assert!(!substs.has_erasable_regions());
    assert!(!substs.needs_subst());

    match inst.def {
        ty::InstanceDef::Item(ty::WithOptConstParam { did: def_id, .. }) |
        ty::InstanceDef::Intrinsic(def_id) => {
            if substs.len() == 0 {
                def_id_str(tcx, def_id)
            } else {
                ext_def_id_str(tcx, def_id, "_inst", substs)
            }
        },
        ty::InstanceDef::VTableShim(def_id) =>
            ext_def_id_str(tcx, def_id, "_vtshim", substs),
        ty::InstanceDef::ReifyShim(def_id) =>
            ext_def_id_str(tcx, def_id, "_reify", substs),
        ty::InstanceDef::Virtual(def_id, idx) =>
            ext_def_id_str(tcx, def_id, &format!("_virt{}_", idx), substs),
        ty::InstanceDef::DropGlue(def_id, _) =>
            ext_def_id_str(tcx, def_id, "_drop", substs),
        ty::InstanceDef::FnPtrShim(def_id, _) |
        ty::InstanceDef::ClosureOnceShim { call_once: def_id, .. } =>
            ext_def_id_str(tcx, def_id, "_callonce", substs),
        ty::InstanceDef::CloneShim(def_id, _) =>
            ext_def_id_str(tcx, def_id, "_shim", substs),
    }
}

pub fn trait_inst_id_str<'tcx>(
    tcx: TyCtxt<'tcx>,
    ti: &TraitInst<'tcx>,
) -> String {
    if let Some(trait_ref) = ti.trait_ref {
        let dyn_ty = ti.dyn_ty(tcx)
            .expect("dyn_ty should only return None when self.trait_ref is None");
        ext_def_id_str(tcx, trait_ref.def_id, "_trait", dyn_ty)
    } else {
        "trait/0::empty[0]".to_owned()
    }
}

/// Get the mangled name of a monomorphic function.  As a side effect, this marks the function as
/// "used", so its body will be emitted too.
pub fn get_fn_def_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    defid: DefId,
    substs: ty::subst::SubstsRef<'tcx>,
) -> String {
    let inst = ty::Instance::resolve(
        mir.state.tcx,
        ty::ParamEnv::reveal_all(),
        defid,
        substs,
    );

    // Compute the mangled name of the monomorphized instance being called.
    if let Ok(Some(inst)) = inst {
        mir.used.instances.insert(inst);
        inst_id_str(mir.state.tcx, inst)
    } else {
        eprintln!(
            "error: failed to resolve FnDef Instance: {:?}, {:?}",
            defid, substs,
        );
        def_id_str(mir.state.tcx, defid)
    }
}

pub fn get_promoted_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    defid: DefId,
    substs: ty::subst::SubstsRef<'tcx>,
    promoted: Option<mir::Promoted>,
) -> String {
    let parent = get_fn_def_name(mir, defid, substs);
    let idx = match promoted {
        Some(x) => x,
        None => return parent,
    };
    format!("{}::{{{{promoted}}}}[{}]", parent, idx.as_usize())
}

pub fn get_drop_fn_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<String> {
    let inst = ty::Instance::resolve_drop_in_place(mir.state.tcx, ty);
    if let ty::InstanceDef::DropGlue(_, None) = inst.def {
        // `None` instead of a `Ty` indicates this drop glue is a no-op.
        return None;
    }
    mir.used.instances.insert(inst);
    Some(inst_id_str(mir.state.tcx, inst))
}

impl ToJson<'_> for hir::def_id::DefId {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        json!(def_id_str(mir.state.tcx, *self))
    }
}

/// rustc's vtables have null entries for non-object-safe methods (those with `Where Self: Sized`).
/// We omit such methods from our vtables.  This function adjusts vtable indices from rustc's way
/// of counting to ours.
fn adjust_method_index<'tcx>(
    tcx: TyCtxt<'tcx>,
    tref: ty::Binder<'tcx, ty::TraitRef<'tcx>>,
    raw_idx: usize,
) -> usize {
    let methods = tcx.vtable_entries(tref);
    methods.iter().take(raw_idx)
        .filter(|m| matches!(m, ty::vtable::VtblEntry::Method(_)))
        .count()
}

impl<'tcx> ToJson<'tcx> for ty::Instance<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let substs = mir.state.tcx.normalize_erasing_regions(
            ty::ParamEnv::reveal_all(),
            self.substs,
        );

        match self.def {
            ty::InstanceDef::Item(did) => json!({
                "kind": "Item",
                "def_id": did.did.to_json(mir),
                "substs": substs.to_json(mir),
            }),
            ty::InstanceDef::Intrinsic(did) => json!({
                "kind": "Intrinsic",
                "def_id": did.to_json(mir),
                "substs": substs.to_json(mir),
            }),
            ty::InstanceDef::VTableShim(did) => json!({
                "kind": "VTableShim",  // NB nightly-2023-01-22 - case change
                "def_id": did.to_json(mir),
                "substs": substs.to_json(mir),
            }),
            ty::InstanceDef::ReifyShim(did) => json!({
                "kind": "ReifyShim",
                "def_id": did.to_json(mir),
                "substs": substs.to_json(mir),
            }),
            ty::InstanceDef::FnPtrShim(did, ty) => json!({
                "kind": "FnPtrShim",
                "def_id": did.to_json(mir),
                "substs": substs.to_json(mir),
                "ty": ty.to_json(mir),
            }),
            ty::InstanceDef::Virtual(did, idx) => {
                let self_ty = substs.types().next()
                    .unwrap_or_else(|| panic!("expected self type in substs for {:?}", self));
                let preds = match *self_ty.kind() {
                    // NB nightly-2022-01-23 - is the addition of dynkind here relevant?
                    ty::TyKind::Dynamic(ref preds, _region, _dynkind) => preds,
                    _ => panic!("expected `dyn` self type, but got {:?}", self_ty),
                };
                let ex_tref = match preds.principal() {
                    Some(x) => x,
                    None => panic!("no principal trait for {:?}?", self_ty),
                };
                let tref = ex_tref.with_self_ty(mir.state.tcx, self_ty);

                let erased_tref = mir.state.tcx.erase_late_bound_regions(tref);
                let ti = TraitInst::from_trait_ref(mir.state.tcx, erased_tref);
                let trait_name = trait_inst_id_str(mir.state.tcx, &ti);
                mir.used.traits.insert(ti);

                json!({
                    "kind": "Virtual",
                    "trait_id": trait_name,
                    "item_id": did.to_json(mir),
                    "index": adjust_method_index(mir.state.tcx, tref, idx),
                })
            },
            ty::InstanceDef::ClosureOnceShim { call_once, .. } => json!({
                "kind": "ClosureOnceShim",
                "call_once": call_once.to_json(mir),
                "substs": substs.to_json(mir),
            }),
            ty::InstanceDef::DropGlue(did, ty) => json!({
                "kind": "DropGlue",
                "def_id": did.to_json(mir),
                "substs": substs.to_json(mir),
                "ty": ty.to_json(mir),
            }),
            ty::InstanceDef::CloneShim(did, ty) => {
                let sub_tys = match *ty.kind() {
                    ty::TyKind::Array(t, _) => vec![t],
                    ty::TyKind::Tuple(ts) => ts[..].to_owned(),
                    ty::TyKind::Closure(closure_did, substs) =>
                        substs.as_closure().upvar_tys().collect(),
                    _ => {
                        eprintln!("warning: don't know how to build clone shim for {:?}", ty);
                        vec![]
                    },
                };
                let callees = sub_tys.into_iter()
                    .map(|ty| {
                        let inst = ty::Instance::resolve(
                            mir.state.tcx,
                            ty::ParamEnv::reveal_all(),
                            did,
                            mir.state.tcx.intern_substs(&[ty.into()]),
                        ).unwrap_or_else(|_| {
                            panic!("failed to resolve instance: {:?}, {:?}", did, ty);
                        });
                        if let Some(inst) = inst {
                            // Add the callee to `used.insances`, so we'll emit code for it even if
                            // it's otherwise unused.  If `inst` is itself a `CloneShim`, its own
                            // callees will be visited when generating the "intrinsics" entry for
                            // `inst`.
                            mir.used.instances.insert(inst.clone());
                        }
                        inst.map(|i| inst_id_str(mir.state.tcx, i))
                    }).collect::<Vec<_>>();
                json!({
                    "kind": "CloneShim",
                    "def_id": did.to_json(mir),
                    "substs": substs.to_json(mir),
                    "ty": ty.to_json(mir),
                    "callees": callees.to_json(mir),
                })
            },
        }
    }
}

// For type _references_. To translate ADT defintions, do it explicitly.
impl<'tcx> ToJson<'tcx> for ty::Ty<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        // If this type has already been interned, just return its ID.
        if let Some(id) = mir.tys.get(*self) {
            return json!(id);
        }

        // Otherwise, convert the type to JSON and add the new entry to the interning table.
        let j = match self.kind() {
            &ty::TyKind::Bool => {
                json!({"kind": "Bool"})
            }
            &ty::TyKind::Char => {
                json!({"kind": "Char"})
            }
            &ty::TyKind::Int(t) => {
                json!({"kind": "Int", "intkind": t.to_json(mir)})
            }
            &ty::TyKind::Uint(t) => {
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
            &ty::TyKind::Float(sz) => {
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
            &ty::TyKind::Adt(adtdef, substs) => {
                let ai = AdtInst::new(adtdef, substs);
                mir.used.types.insert(ai);
                json!({
                    "kind": "Adt",
                    "name": adt_inst_id_str(mir.state.tcx, ai),
                    "orig_def_id": adtdef.did().to_json(mir),
                    "substs": substs.to_json(mir),
                })
            }
            &ty::TyKind::FnDef(defid, ref substs) => {
                let name = get_fn_def_name(mir, defid, substs);
                json!({
                    "kind": "FnDef",
                    "defid": name,
                })
            }
            &ty::TyKind::Param(..) => unreachable!(
                "no TyKind::Param should remain after monomorphization"
            ),
            &ty::TyKind::Closure(defid, ref substs) => {
                json!({
                    "kind": "Closure",
                    "upvar_tys": substs.as_closure().upvar_tys()
                        .collect::<Vec<_>>().to_json(mir),
                    // mir-verifier uses the same representation for closures as it does for
                    // tuples, so no additional information is needed.
                })
            }
            // NB nightly-2022-01-23 - is the addition of dynkind here relevant?
            &ty::TyKind::Dynamic(preds, _region, _dynkind) => {
                let ti = TraitInst::from_dynamic_predicates(mir.state.tcx, preds);
                let trait_name = trait_inst_id_str(mir.state.tcx, &ti);
                mir.used.traits.insert(ti);
                json!({
                    "kind": "Dynamic",
                    "trait_id": trait_name,
                    "predicates": preds.iter().map(|p| p.skip_binder().to_json(mir))
                        .collect::<Vec<_>>(),
                })
            }
            &ty::TyKind::Alias(ty::AliasKind::Projection, _) => unreachable!(
                "no TyKind::Alias with AliasKind Projection should remain after monomorphization"
            ),
            &ty::TyKind::FnPtr(ref sig) => {
                json!({"kind": "FnPtr", "signature": sig.to_json(mir)})
            }
            &ty::TyKind::Never => {
                json!({"kind": "Never"})
            }
            &ty::TyKind::Error(_) => {
                json!({"kind": "Error"})
            }
            &ty::TyKind::Infer(_) => {
                // TODO
                json!({"kind": "Infer"})
            }
            &ty::TyKind::Bound(_, _) => {
                // TODO
                json!({"kind": "Bound"})
            }
            &ty::TyKind::Placeholder(_) => {
                // TODO
                json!({"kind": "Placeholder"})
            }
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
            // NB nightly-2023-01-22 - is this correct?
            &ty::TyKind::Alias(ty::AliasKind::Opaque, _) => {
                // TODO
                json!({"kind": "Alias"})
            }
        };

        let id = mir.tys.insert(*self, j);
        json!(id)
    }
}

impl ToJson<'_> for ty::ParamTy {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(self.index)
    }
}

impl<'tcx> ToJson<'tcx> for ty::PolyFnSig<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let sig = ms.state.tcx.erase_late_bound_regions(*self);
        sig.to_json(ms)
    }
}

impl<'tcx> ToJson<'tcx> for ty::FnSig<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let input_jsons : Vec<serde_json::Value> =
            self.inputs().iter().map(|i| i.to_json(ms)).collect();
        json!({
            "inputs": input_jsons,
            "output": self.output().to_json(ms),
            "abi": self.abi.to_json(ms),
        })
    }
}

impl<'tcx> ToJson<'tcx> for ty::TraitRef<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "trait":  self.def_id.to_json(ms),
            "substs":  self.substs.to_json(ms)
        })
    }
}

impl<'tcx> ToJson<'tcx> for ty::AliasTy<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "substs": self.substs.to_json(ms),
            "def_id": self.def_id.to_json(ms)  // NB nightly-2023-01-22 - field name change
        })
    }
}

// Predicate (static / `where` clause)

impl<'tcx> ToJson<'tcx> for ty::Predicate<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self.kind().skip_binder() {
            // NB: nightly-2023-01-23 is this right?
            ty::PredicateKind::Clause(ty::Clause::Trait(tp)) => {
                json!({
                    "trait_pred": tp.trait_ref.to_json(ms)
                })
            }
            ty::PredicateKind::Clause(ty::Clause::Projection(pp)) => match pp.term.unpack() {
                ty::TermKind::Ty(ty) => json!({
                    "projection_ty": pp.projection_ty.to_json(ms),
                    "ty": ty.to_json(ms),
                }),
                ty::TermKind::Const(_) => json!("unknown_const_projection"),
            }
            _ => {
                json!("unknown_pred")
            }
        }
    }
}

// Existential predicate (dynamic / trait object version of `ty::Predicate`)

impl<'tcx> ToJson<'tcx> for ty::ExistentialPredicate<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &ty::ExistentialPredicate::Trait(ref trait_ref) => {
                json!({
                    "kind": "Trait",
                    "trait": trait_ref.def_id.to_json(ms),
                    "substs": trait_ref.substs.to_json(ms),
                })
            },
            &ty::ExistentialPredicate::Projection(ref proj) => match proj.term.unpack() {
                ty::TermKind::Ty(ty) => json!({
                    "kind": "Projection",
                    "proj": proj.def_id.to_json(ms),
                    "substs": proj.substs.to_json(ms),
                    "rhs_ty": ty.to_json(ms),
                }),
                ty::TermKind::Const(_) => json!({
                    "kind": "Projection_Const",
                }),
            },
            &ty::ExistentialPredicate::AutoTrait(ref did) => {
                json!({
                    "kind": "AutoTrait",
                    "trait": did.to_json(ms),
                })
            },
        }
    }
}


impl<'tcx> ToJson<'tcx> for ty::GenericPredicates<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        fn gather_preds<'tcx>(
            ms: &mut MirState<'_, 'tcx>,
            preds: &ty::GenericPredicates<'tcx>,
            dest: &mut Vec<serde_json::Value>,
        ) {
            dest.extend(preds.predicates.iter().map(|p| p.0.to_json(ms)));
            if let Some(parent_id) = preds.parent {
                let parent_preds = ms.state.tcx.predicates_of(parent_id);
                gather_preds(ms, &parent_preds, dest);
            }
        }

        let mut json_preds: Vec<serde_json::Value> = Vec::new();
        gather_preds(ms, self, &mut json_preds);
        json!({ "predicates": json_preds })
    }
}

impl ToJson<'_> for ty::GenericParamDef {
    fn to_json(&self, ms: &mut MirState) -> serde_json::Value {
        json!({
            "param_def": *(self.name.as_str()),
            "def_id": self.def_id.to_json(ms),
        }) // TODO
    }
}

impl ToJson<'_> for ty::Generics {
    fn to_json(&self, ms: &mut MirState) -> serde_json::Value {
        fn gather_params(
            ms: &mut MirState,
            generics: &ty::Generics,
            dest: &mut Vec<serde_json::Value>,
        ) {
            if let Some(parent_id) = generics.parent {
                let parent_generics = ms.state.tcx.generics_of(parent_id);
                gather_params(ms, &parent_generics, dest);
            }
            dest.extend(generics.params.iter().map(|p| p.to_json(ms)));
        }

        let mut json_params: Vec<serde_json::Value> = Vec::new();
        gather_params(ms, self, &mut json_params);
        json!({
            "params": json_params
        }) // TODO
    }
}

pub trait ToJsonAg {
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> serde_json::Value;
}

impl<'tcx> ToJson<'tcx> for ty::subst::GenericArg<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self.unpack() {
            ty::subst::GenericArgKind::Type(ref ty) => ty.to_json(mir),
            // In mir-verifier, all substs entries are considered "types", and there are dummy
            // TyLifetime and TyConst variants to handle non-type entries.  We emit something that
            // looks vaguely like an interned type's ID here, and handle it specially in MIR.JSON.
            ty::subst::GenericArgKind::Lifetime(_) => json!("nonty::Lifetime"),
            ty::subst::GenericArgKind::Const(_) => json!("nonty::Const"),
        }
    }
}

fn eval_array_len<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: ty::Const<'tcx>,
) -> usize {
    match c.kind() {
        // ty::ConstKind::Unevaluated(un) => {
        //     tcx.const_eval_resolve(ty::ParamEnv::reveal_all(), un.expand(), None).unwrap()
        // },
        // NB: the type of "val" changed to valtree - try to get the size out of that
        ty::ConstKind::Value(ty::ValTree::Leaf(val)) =>
            val.try_to_machine_usize(tcx).expect("expecting usize value from constant") as usize,
        ref val => panic!("don't know how to translate ConstKind::{:?}", val),
    }
    // match evaluated {
    //     interpret::ConstValue::Scalar(interpret::Scalar::Int(sint)) => {
    //         let data = sint.to_bits(sint.size()).unwrap();
    //         assert!(data <= usize::MAX as u128);
    //         data as usize
    //     },
    //     _ => panic!("impossible: array size is not a scalar?"),
    // }
}

fn read_static_memory<'tcx>(
    alloc: &'tcx mir::interpret::Allocation,
    start: usize,
    end: usize,
) -> &'tcx [u8] {
    // NB: nightly-2023-01-22 - is this correct?
    assert!(alloc.provenance().ptrs().len() == 0);
    alloc.inspect_with_uninit_and_ptr_outside_interpreter(start .. end)
}

fn render_constant_scalar<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    ty: ty::Ty<'tcx>,
    s: interpret::Scalar,
) -> Option<serde_json::Value> {
    match s {
        interpret::Scalar::Int(sint) => {
            let data = sint.to_bits(sint.size()).unwrap();
            render_constant(mir, ty, Some(s), Some((sint.size().bytes() as u8, data)), None)
        },
        interpret::Scalar::Ptr(ptr, _) => {
            match mir.state.tcx.try_get_global_alloc(ptr.provenance) {
                Some(ga) => match ga {
                    interpret::GlobalAlloc::Static(def_id) => Some(json!({
                        "kind": "static_ref",
                        "def_id": def_id.to_json(mir),
                    })),
                    interpret::GlobalAlloc::Memory(alloc) => {
                        let start = ptr.into_parts().1.bytes() as usize;
                        render_constant(
                            mir,
                            ty,
                            Some(s),
                            None,
                            Some((alloc.inner(), start, start)),
                        )
                    },
                    _ => None,
                },
                None => None,
            }
        },
    }
}

fn render_zst<'tcx>() -> serde_json::Value {
    json!({
        "kind": "zst",
    })
}

// TODO: migrate all constant rendering to use InterpCx + OpTy.  This should reduce special cases
// and let us handle both in-memory and immediate constants.
fn render_constant<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    ty: ty::Ty<'tcx>,
    scalar: Option<interpret::Scalar>,
    scalar_bits: Option<(u8, u128)>,
    slice: Option<(&'tcx mir::interpret::Allocation, usize, usize)>,
) -> Option<serde_json::Value> {
    // Special cases: &str and &[u8; _]
    if let ty::TyKind::Ref(_, inner_ty, hir::Mutability::Not) = *ty.kind() {
        if let ty::TyKind::Str = *inner_ty.kind() {
            // String literal
            let (alloc, start, end) = slice.expect("string const had non-slice value");
            let mem = read_static_memory(alloc, start, end);
            return Some(json!({
                "kind": "str",
                "val": mem,
            }));
        }

        if let ty::TyKind::Array(elem_ty, len_const) = *inner_ty.kind() {
            if let ty::TyKind::Uint(ty::UintTy::U8) = *elem_ty.kind() {
                // Bytestring literal
                let len = eval_array_len(mir.state.tcx, len_const);
                let (alloc, start, _) = slice.expect("string const had non-slice value");
                let end = start + len;
                let mem = read_static_memory(alloc, start, end);
                return Some(json!({
                    "kind": "bstr",
                    "val": mem,
                }));
            }
        }
    }

    Some(match *ty.kind() {
        ty::TyKind::Int(_) => {
            let (size, bits) = scalar_bits.expect("int const had non-scalar value?");
            let mut val = bits as i128;
            if bits & (1 << (size * 8 - 1)) != 0 && size < 128 / 8 {
                // Sign-extend to 128 bits
                val |= -1_i128 << (size * 8);
            }
            json!({
                "kind": match *ty.kind() {
                    ty::TyKind::Int(ty::IntTy::Isize) => "isize",
                    ty::TyKind::Int(_) => "int",
                    _ => unreachable!(),
                },
                "size": size,
                "val": val.to_string(),
            })
        },
        ty::TyKind::Bool |
        ty::TyKind::Char |
        ty::TyKind::Uint(_) => {
            let (size, bits) = scalar_bits.expect("uint const had non-scalar value?");
            json!({
                "kind": match *ty.kind() {
                    ty::TyKind::Bool => "bool",
                    ty::TyKind::Char => "char",
                    ty::TyKind::Uint(ty::UintTy::Usize) => "usize",
                    ty::TyKind::Uint(_) => "uint",
                    _ => unreachable!(),
                },
                "size": size,
                "val": bits.to_string(),
            })
        },
        ty::TyKind::Float(ty::FloatTy::F32) => {
            let (size, bits) = scalar_bits.expect("f32 const had non-scalar value?");
            let val = f32::from_bits(bits as u32);
            json!({
                "kind": "float",
                "size": size,
                "val": val.to_string(),
            })
        },
        ty::TyKind::Float(ty::FloatTy::F64) => {
            let (size, bits) = scalar_bits.expect("f64 const had non-scalar value?");
            let val = f64::from_bits(bits as u64);
            json!({
                "kind": "float",
                "size": size,
                "val": val.to_string(),
            })
        },

        ty::TyKind::RawPtr(_) => {
            let (_size, bits) =
                match scalar_bits {
                    Some(s) => s,
                    None => return None
                };

            json!({
                "kind": "raw_ptr",
                "val": bits.to_string(),
            })
        },

        ty::TyKind::FnDef(defid, ref substs) => {
            json!({
                "kind": "fndef",
                "def_id": get_fn_def_name(mir, defid, substs),
            })
        },

        ty::TyKind::Adt(adt_def, _substs) if adt_def.is_struct() => {
            let tyl = mir.state.tcx.layout_of(ty::ParamEnv::reveal_all().and(ty))
                .unwrap_or_else(|e| panic!("failed to get layout of {:?}: {}", ty, e));
            let scalar = scalar.expect("adt had non-scalar value (NYI)");
            let variant = adt_def.non_enum_variant();
            json!({
                "kind": "struct",
                "fields": render_constant_variant(
                    mir,
                    variant,
                    interpret::ImmTy::from_scalar(scalar, tyl).into(),
                ),
            })
        },

        ty::TyKind::Adt(adt_def, _substs) if adt_def.is_enum() => {
            let tyl = mir.state.tcx.layout_of(ty::ParamEnv::reveal_all().and(ty))
                .unwrap_or_else(|e| panic!("failed to get layout of {:?}: {}", ty, e));
            let scalar = scalar.expect("adt had non-scalar value (NYI)");

            let icx = interpret::InterpCx::new(
                mir.state.tcx,
                DUMMY_SP,
                ty::ParamEnv::reveal_all(),
                RenderConstMachine,
            );
            let op_ty = interpret::ImmTy::from_scalar(scalar, tyl).into();
            let (_discr, variant_idx) = icx.read_discriminant(&op_ty).unwrap_or_else(|e| {
                panic!("failed to access discriminant of {:?}: {}", op_ty.layout.ty, e)
            });

            let variant = &adt_def.variants()[variant_idx];
            json!({
                "kind": "enum",
                "variant": variant_idx.as_u32(),
                "fields": render_constant_variant(
                    mir,
                    variant,
                    icx.operand_downcast(&op_ty, variant_idx).unwrap_or_else(|e| {
                        panic!("failed to downcast {:?} to variant {:?}: {}",
                            op_ty.layout.ty, variant_idx, e)
                    }),
                ),
            })
        },

        _ => {
            if let Some((0, _)) = scalar_bits {
                render_zst()
            } else {
                return None;
            }
        },
    })
}

fn render_constant_variant<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    variant: &'tcx ty::VariantDef,
    op_ty: interpret::OpTy<'tcx>,
) -> Option<serde_json::Value> {
    let icx = interpret::InterpCx::new(
        mir.state.tcx,
        DUMMY_SP,
        ty::ParamEnv::reveal_all(),
        RenderConstMachine,
    );
    let mut vals = Vec::with_capacity(variant.fields.len());
    for i in 0 .. variant.fields.len() {
        let field = icx.operand_field(&op_ty, i).unwrap_or_else(|e| {
            panic!("failed to access field {} of {:?}: {}", i, op_ty.layout.ty, e)
        });

        // `try_as_mplace` always "succeeds" (returns an `MPlace`, dangling) for ZSTs.  We want it
        // to be an immediate instead.
        if field.layout.is_zst() {
            // NB nightly-2022-01-23 : ZST is gone?
            // call render_constant directly such that it returns a zst value
            vals.push(render_zst());
            continue;
        }

        let val = match field.as_mplace_or_imm().into() {
            Err(_mpl) => None,
            Ok(imm) =>
                match *imm {
                    interpret::Immediate::Scalar(s) =>
                            render_constant_scalar(mir, field.layout.ty, s),
                    _ => None,
                }
        }?;
        vals.push(val);
    }
    Some(vals.into())
}

struct RenderConstMachine;

mod machine {
    use std::borrow::Cow;
    use super::*;
    use rustc_const_eval::interpret::*;
    use rustc_data_structures::fx::FxIndexMap;
    use rustc_middle::ty::*;
    use rustc_middle::mir::*;
    use rustc_span::Span;
    use rustc_target::abi::Size;
    use rustc_target::spec::abi::Abi;

    impl<'mir, 'tcx> Machine<'mir, 'tcx> for RenderConstMachine {
        type MemoryKind = !;
        type Provenance = AllocId;
        type ProvenanceExtra = ();
        type ExtraFnVal = !;
        type FrameExtra = ();
        type AllocExtra = ();
        type MemoryMap = FxIndexMap<
            AllocId,
            (MemoryKind<!>, Allocation),
        >;

        const GLOBAL_KIND: Option<Self::MemoryKind> = None;
        const PANIC_ON_ALLOC_FAIL: bool = false;

        fn enforce_alignment(ecx: &InterpCx<'mir, 'tcx, Self>) -> CheckAlignment {
            CheckAlignment::No
        }

        fn alignment_check_failed(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            has: Align,
            required: Align,
            check: CheckAlignment,
        ) -> InterpResult<'tcx, ()> {
            panic!("not implemented: alignment_check_failed");
        }

        fn use_addr_for_alignment_check(ecx: &InterpCx<'mir, 'tcx, Self>) -> bool {
            false
        }

        #[inline(always)]
        fn checked_binop_checks_overflow(_ecx: &InterpCx<'mir, 'tcx, Self>) -> bool {
            true
        }

        fn enforce_validity(ecx: &InterpCx<'mir, 'tcx, Self>) -> bool {
            false
        }

        // fn enforce_number_init(ecx: &InterpCx<'mir, 'tcx, Self>) -> bool {
        //     false
        // }

        // fn enforce_number_no_provenance(ecx: &InterpCx<'mir, 'tcx, Self>) -> bool {
        //     false
        // }

        fn find_mir_or_eval_fn(
            ecx: &mut InterpCx<'mir, 'tcx, Self>,
            instance: ty::Instance<'tcx>,
            abi: Abi,
            args: &[OpTy<'tcx, Self::Provenance>],
            destination: &PlaceTy<'tcx, Self::Provenance>,
            target: Option<mir::BasicBlock>,
            unwind: StackPopUnwind,
        ) -> InterpResult<'tcx, Option<(&'mir mir::Body<'tcx>, ty::Instance<'tcx>)>> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "find_mir_or_eval_fn".into(),
                ),
            ).into())
        }

        fn call_extra_fn(
            ecx: &mut InterpCx<'mir, 'tcx, Self>,
            fn_val: Self::ExtraFnVal,
            abi: Abi,
            args: &[OpTy<'tcx, Self::Provenance>],
            destination: &PlaceTy<'tcx, Self::Provenance>,
            target: Option<mir::BasicBlock>,
            unwind: StackPopUnwind,
        ) -> InterpResult<'tcx> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "call_extra_fn".into(),
                ),
            ).into())
        }

        fn call_intrinsic(
            ecx: &mut InterpCx<'mir, 'tcx, Self>,
            instance: ty::Instance<'tcx>,
            args: &[OpTy<'tcx, Self::Provenance>],
            destination: &PlaceTy<'tcx, Self::Provenance>,
            target: Option<mir::BasicBlock>,
            unwind: StackPopUnwind,
        ) -> InterpResult<'tcx> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "call_intrinsic".into(),
                ),
            ).into())
        }

        fn assert_panic(
            ecx: &mut InterpCx<'mir, 'tcx, Self>,
            msg: &mir::AssertMessage<'tcx>,
            unwind: Option<mir::BasicBlock>,
        ) -> InterpResult<'tcx> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "assert_panic".into(),
                ),
            ).into())
        }

        fn binary_ptr_op(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            bin_op: mir::BinOp,
            left: &ImmTy<'tcx, Self::Provenance>,
            right: &ImmTy<'tcx, Self::Provenance>,
        ) -> InterpResult<'tcx, (Scalar<Self::Provenance>, bool, Ty<'tcx>)> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "binary_ptr_op".into(),
                ),
            ).into())
        }

        fn extern_static_base_pointer(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            def_id: DefId,
        ) -> InterpResult<'tcx, Pointer<Self::Provenance>> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "extern_static_base_pointer".into(),
                ),
            ).into())
        }

        fn adjust_alloc_base_pointer(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            ptr: Pointer,
        ) -> Pointer<Self::Provenance> {
            unimplemented!("tag_alloc_base_pointer")
        }

        fn ptr_from_addr_cast(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            addr: u64,
        ) -> InterpResult<'tcx, Pointer<Option<Self::Provenance>>> {
            unimplemented!("ptr_from_addr_cast")
        }

        fn expose_ptr(
            ecx: &mut InterpCx<'mir, 'tcx, Self>,
            ptr: Pointer<Self::Provenance>,
        ) -> InterpResult<'tcx> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "expose_ptr".into(),
                ),
            ).into())
        }

        fn ptr_get_alloc(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            ptr: Pointer<Self::Provenance>,
        ) -> Option<(AllocId, Size, Self::ProvenanceExtra)> {
            None
        }

        fn adjust_allocation<'b>(
            ecx: &InterpCx<'mir, 'tcx, Self>,
            id: AllocId,
            alloc: Cow<'b, Allocation>,
            kind: Option<MemoryKind<Self::MemoryKind>>,
        ) -> InterpResult<'tcx, Cow<'b, Allocation<Self::Provenance, Self::AllocExtra>>> {
            Ok(alloc)
        }

        fn init_frame_extra(
            ecx: &mut InterpCx<'mir, 'tcx, Self>,
            frame: Frame<'mir, 'tcx, Self::Provenance>,
        ) -> InterpResult<'tcx, Frame<'mir, 'tcx, Self::Provenance, Self::FrameExtra>> {
            Err(InterpError::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "init_frame_extra".into(),
                ),
            ).into())
        }

        fn stack<'a>(
            ecx: &'a InterpCx<'mir, 'tcx, Self>,
        ) -> &'a [Frame<'mir, 'tcx, Self::Provenance, Self::FrameExtra>] {
            unimplemented!("stack")
        }

        fn stack_mut<'a>(
            ecx: &'a mut InterpCx<'mir, 'tcx, Self>,
        ) -> &'a mut Vec<Frame<'mir, 'tcx, Self::Provenance, Self::FrameExtra>> {
            unimplemented!("stack_mut")
        }
    }
}

impl<'tcx> ToJson<'tcx> for ty::Const<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut map = serde_json::Map::new();
        map.insert("ty".to_owned(), self.ty().to_json(mir));

        match self.kind() {
            // remove? should probably not show up?
            ty::ConstKind::Unevaluated(un) => {
                map.insert("initializer".to_owned(), json!({
                    // TODO nightly-2023-01-22 promoted has been removed?
                    // change `get_promoted_name` to the "get non-promoted name" version
                    // if we even need this case
                    "def_id": get_fn_def_name(mir, un.def.did, un.substs),
                }));
            },
            _ => {},
        }

        // let evaluated = match self.kind() {
        //     // nightly-2023-01-22 remove?  probably should not show up
        //     ty::ConstKind::Unevaluated(un) => {
        //         // TODO nightly-2023-01-22 unevaluatedconst changed
        //         // use `const_eval_resolve_for_typecheck` ?
        //         mir.state.tcx.const_eval_resolve(ty::ParamEnv::reveal_all(), un, None).unwrap()
        //     },
        //     // TODO nightly-2023-01-22 ConstKind value is now a valtree (assume leaf only?)
        //     // Remove other cases besides Value(Leaf(x)) - this means we might remove slice below
        //     // might have to see if we panic
        //     ty::ConstKind::Value(val) => val,
        //     _ => panic!("don't know how to translate ConstKind::{:?}", self.kind()),
        // };

        // let rendered = match evaluated {
        //     interpret::ConstValue::Scalar(s) => {
        //         render_constant_scalar(mir, self.ty(), s)
        //     },
        //     interpret::ConstValue::Slice { data, start, end } => {
        //         render_constant(mir, self.ty(), None, None, Some((data.inner(), start, end)))
        //     },
        //     _ => None,
        // };

        let rendered = match self.kind() {
            ty::ConstKind::Value(ty::ValTree::Leaf(val)) =>
                render_constant(mir, self.ty(), None, Some((val.size().bytes() as u8, val.try_to_uint(val.size()).unwrap())), None),
            _ => panic!("don't know how to translate ConstKind::{:?}", self.kind())
        };
        if let Some(rendered) = rendered {
            map.insert("rendered".to_owned(), rendered);
        }

        map.into()
    }
}

impl<'tcx> ToJson<'tcx> for (interpret::ConstValue<'tcx>, ty::Ty<'tcx>) {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let (val, ty) = *self;
        match val {
            interpret::ConstValue::Scalar(s) => {
                render_constant_scalar(mir, ty, s)
                    .unwrap_or_else(|| json!({"type": "unknown_scalar"}))
            },
            interpret::ConstValue::Slice { data, start, end } => {
                render_constant(mir, ty, None, None, Some((data.inner(), start, end)))
                    .unwrap_or_else(|| json!({"type": "unknown_slice"}))
            },
            interpret::ConstValue::ZeroSized => {
                render_zst()
            },
            interpret::ConstValue::ByRef { .. } => json!({"kind": "unknown_by_ref"}),
        }
    }
}

fn iter_tojson<'a, 'tcx, I, V: 'a>(
    it: I,
    mir: &mut MirState<'_, 'tcx>,
    substs: ty::subst::SubstsRef<'tcx>,
) -> serde_json::Value
where I: Iterator<Item = &'a V>, V: ToJsonAg {
    let mut j = Vec::with_capacity(it.size_hint().0);
    for v in it {
        j.push(v.tojson(mir, substs));
    }
    json!(j)
}

impl<T> ToJsonAg for [T]
where
    T: ToJsonAg,
{
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> serde_json::Value {
        iter_tojson(self.iter(), mir, substs)
    }
}

impl<T> ToJsonAg for Vec<T>
where
    T: ToJsonAg,
{
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> serde_json::Value {
        <[T] as ToJsonAg>::tojson(self, mir, substs)
    }
}

impl<I, T> ToJsonAg for IndexVec<I, T>
where
    I: Idx,
    T: ToJsonAg,
{
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> serde_json::Value {
        iter_tojson(self.iter(), mir, substs)
    }
}

pub fn is_adt_ak(ak: &mir::AggregateKind) -> bool {
    match ak {
        &mir::AggregateKind::Adt(_, _, _, _, _) => true,
        _ => false,
    }
}

impl<'tcx> ToJson<'tcx> for AdtInst<'tcx> {
    fn to_json(
        &self,
        mir: &mut MirState<'_, 'tcx>,
    ) -> serde_json::Value {
        let ty = mir.state.tcx.mk_adt(self.adt, self.substs);
        let tyl = mir.state.tcx.layout_of(ty::ParamEnv::reveal_all().and(ty))
            .unwrap_or_else(|e| panic!("failed to get layout of {:?}: {}", ty, e));
        json!({
            "name": adt_inst_id_str(mir.state.tcx, *self),
            "kind": format!("{:?}", self.adt.adt_kind()),
            "variants": self.adt.variants().tojson(mir, self.substs),
            "size": tyl.size.bytes(),
            "repr_transparent": self.adt.repr().transparent(),
            "orig_def_id": self.adt.did().to_json(mir),
            "orig_substs": self.substs.to_json(mir),
        })
    }
}

impl ToJsonAg for ty::VariantDef {
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> serde_json::Value {
        json!({
            "name": self.def_id.to_json(mir),
            "discr": self.discr.to_json(mir),
            "fields": self.fields.tojson(mir, substs),
            "ctor_kind": self.ctor_kind().to_json(mir)
        })
    }
}

impl ToJsonAg for ty::FieldDef {
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        substs: ty::subst::SubstsRef<'tcx>,
    ) -> serde_json::Value {
        let unsubst_ty = mir.state.tcx.type_of(self.did);
        let ty = mir.state.tcx.subst_and_normalize_erasing_regions(
            substs, ty::ParamEnv::reveal_all(), unsubst_ty);
        json!({
            "name": self.did.to_json(mir),
            "ty": ty.to_json(mir),
        })
    }
}

pub fn handle_adt_ag<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    ak: &mir::AggregateKind<'tcx>,
    opv: &Vec<mir::Operand<'tcx>>,
) -> serde_json::Value {
    match ak {
        &mir::AggregateKind::Adt(adt_did, variant, substs, _, _) => {
            let adt = mir.state.tcx.adt_def(adt_did);
            json!({
                "adt": AdtInst::new(adt, substs).to_json(mir),
                "variant": variant.to_json(mir),
                "ops": opv.to_json(mir)
            })
        }
        _ => unreachable!("bad"),
    }
}

pub fn eval_mir_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &mir::Constant<'tcx>,
) -> interpret::ConstValue<'tcx> {
    // let ct = self.monomorphize(constant.literal);
    let uv = match constant.literal {
        mir::ConstantKind::Ty(ct) => match ct.kind() {
            ty::ConstKind::Unevaluated(uv) => uv.expand(),
            ty::ConstKind::Value(val) => {
                return tcx.valtree_to_const_val((ct.ty(), val));
            }
            err => panic!(
                // constant.span,
                "encountered bad ConstKind after monomorphizing: {:?} span:{:?}",
                err, constant.span
            ),
        },
        mir::ConstantKind::Unevaluated(uv, _) => uv,
        mir::ConstantKind::Val(val, _) => return val,
    };

    tcx.const_eval_resolve(ty::ParamEnv::reveal_all(), uv, None).unwrap() // .map_err(|err| {
    //     match err {
    //         ErrorHandled::Reported(_) => {
    //             self.cx.tcx().sess.emit_err(errors::ErroneousConstant { span: constant.span });
    //         }
    //         ErrorHandled::TooGeneric => {
    //             self.cx
    //                 .tcx()
    //                 .sess
    //                 .diagnostic()
    //                 .emit_bug(errors::PolymorphicConstantTooGeneric { span: constant.span });
    //         }
    //     }
    //     err
    // }).unwrap()
}