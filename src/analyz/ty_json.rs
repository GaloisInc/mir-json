use rustc_data_structures::stable_hasher::{HashStable, StableHasher};
use rustc_hashes::Hash64;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_hir::lang_items::LangItem;
use rustc_index::{IndexVec, Idx};
use rustc_middle::mir;
use rustc_middle::ty::CoroutineArgsExt;
use rustc_const_eval::interpret::{
    self, InterpCx, InterpResult, MemPlaceMeta, MPlaceTy, OffsetMode,
    Projectable,
};
use rustc_middle::ty;
use rustc_middle::ty::{AdtKind, DynKind, TyCtxt, TypeVisitableExt};
use rustc_middle::ty::util::IntTypeExt;
use rustc_query_system::ich::StableHashingContext;
use rustc_abi::{Align, ExternAbi, FieldIdx, Size};
use rustc_span::DUMMY_SP;
use serde_json;
use std::usize;

use analyz::merge;
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

impl ToJson<'_> for mir::BorrowKind {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::BorrowKind::Shared => json!("Shared"),
            // "An immutable, aliasable borrow that is discarded after borrow-checking. Can behave
            // either like a normal shared borrow or like a special shallow borrow (see
            // `FakeBorrowKind`)."  We thus treat it like `Shared`.
            &mir::BorrowKind::Fake(_) => json!("Shared"),
            &mir::BorrowKind::Mut { kind: _ } => json!("Mut"),
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

/// For some categories of lang items, we replace the normal `DefId` with `$lang::Foo`.  This gives
/// the item a stable name that we can reference within crucible-mir.
///
/// Currently, we do this only for ADTs.  We only really need it for `core::cmp::Ordering`, but
/// covering all ADTs is easier and more consistent.  We don't use `$lang` paths for functions
/// because it's not needed at the moment and would require a bunch of changes to paths in
/// `TransCustom.hs`.
fn rename_as_lang_item(tcx: TyCtxt, def_id: hir::def_id::DefId) -> Option<LangItem> {
    let lang = tcx.as_lang_item(def_id)?;
    let use_lang_path = matches!(
        lang.target(),
        hir::Target::Enum | hir::Target::Struct | hir::Target::Union,
    );
    if use_lang_path {
        Some(lang)
    } else {
        None
    }
}

/// Render the given `DefId` into a `String` of the form
/// `<crate_name>/<disambig>::<defpath>`. The "orig" in the name
/// `orig_def_id_str` indicates that this will always pick the _original_
/// `DefId` for rendering purposes, even for
/// [lang items](https://doc.rust-lang.org/unstable-book/language-features/lang-items.html).
/// See [`lang_item_def_id_str`] for a variant of this function that renders
/// lang items differently.
///
/// Usually, you will want to use [`def_id_str`] instead, which renders the
/// `DefId` differently depending on whether it is for a lang item or not.
pub fn orig_def_id_str(
    tcx: TyCtxt,
    def_id: hir::def_id::DefId,
) -> String {
    // Based on rustc/ty/context.rs.html TyCtxt::def_path_debug_str
    let crate_name = tcx.crate_name(def_id.krate);
    let disambig = tcx.crate_hash(def_id.krate);
    let defpath = tcx.def_path(def_id);
    format!(
        "{}/{}{}",
        crate_name,
        // Keep this in sync with how disambiguators are formatted in
        // AllocIntern::insert in src/analyz/to_json.rs.
        &disambig.to_string()[..8],
        defpath.to_string_no_crate_verbose(),
    )
}

/// If the given `DefId` is for a
/// [lang item](https://doc.rust-lang.org/unstable-book/language-features/lang-items.html),
/// then return `Some(id_str)`, where `id_str` will be of the form
/// `$lang/0::<lang_item_name>`. Otherwise, return `None`. See
/// [`orig_def_id_str`] for a variant of this function that always renders the
/// original `DefId`.
///
/// Usually, you will want to use [`def_id_str`] instead, which renders the
/// `DefId` differently depending on whether it is for a lang item or not.
pub fn lang_item_def_id_str(
    tcx: TyCtxt,
    def_id: hir::def_id::DefId,
) -> Option<String> {
    rename_as_lang_item(tcx, def_id).map(|lang| format!("$lang/0::{:?}", lang))
}

/// Render the given `DefId` into a `String` of the form
/// `<crate_name>/<disambig>::<defpath>`. If the `DefId` is for a
/// [lang item](https://doc.rust-lang.org/unstable-book/language-features/lang-items.html),
/// then this function will return the lang item's rendered `String`. Otherwise,
/// this will fall back to the original, fully qualified path when rendering the
/// `DefId`.
pub fn def_id_str(
    tcx: TyCtxt,
    def_id: hir::def_id::DefId,
) -> String {
    lang_item_def_id_str(tcx, def_id)
      .unwrap_or_else(|| orig_def_id_str(tcx, def_id))
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
    let hash: Hash64 = tcx.with_stable_hashing_context(|mut hcx| {
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
    // For lang items that have no generics, we omit the unpredictable hash from the `_adtXXX`
    // segment at the end.  This lets us mention the name in crucible-mir.
    if rename_as_lang_item(tcx, ai.def_id()).is_some() && tcx.generics_of(ai.def_id()).is_empty() {
        let base = def_id_str(tcx, ai.def_id());
        return format!("{}::_adt[0]", base);
    }

    // Erase all early-bound regions.
    let args = tcx.erase_and_anonymize_regions(ai.args);
    ext_def_id_str(tcx, ai.def_id(), "_adt", args)
}

pub fn inst_id_str<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: impl Into<FnInst<'tcx>>,
) -> String {
    match inst.into() {
        FnInst::Real(inst) => {
            let args = tcx.normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                inst.args,
            );
            assert!(!args.has_erasable_regions());
            assert!(!args.has_param());
            match inst.def {
                ty::InstanceKind::Item(def_id) |
                ty::InstanceKind::Intrinsic(def_id) => {
                    if args.len() == 0 {
                        def_id_str(tcx, def_id)
                    } else {
                        ext_def_id_str(tcx, def_id, "_inst", args)
                    }
                },
                ty::InstanceKind::VTableShim(def_id) =>
                    ext_def_id_str(tcx, def_id, "_vtshim", args),
                ty::InstanceKind::ReifyShim(def_id, _reason) =>
                    ext_def_id_str(tcx, def_id, "_reify", args),
                ty::InstanceKind::Virtual(def_id, idx) =>
                    ext_def_id_str(tcx, def_id, &format!("_virt{}_", idx), args),
                ty::InstanceKind::DropGlue(def_id, _) =>
                    ext_def_id_str(tcx, def_id, "_drop", args),
                ty::InstanceKind::FnPtrShim(def_id, _) =>
                    ext_def_id_str(tcx, def_id, "_fnptr", args),
                ty::InstanceKind::ClosureOnceShim { call_once: def_id, .. } =>
                    ext_def_id_str(tcx, def_id, "_callonce", args),
                ty::InstanceKind::CloneShim(def_id, _) =>
                    ext_def_id_str(tcx, def_id, "_shim", args),
                ty::InstanceKind::ConstructCoroutineInClosureShim {
                    coroutine_closure_def_id, ..
                } => ext_def_id_str(tcx, coroutine_closure_def_id, "_corocallonce", args),
                ty::InstanceKind::ThreadLocalShim(def_id) =>
                    ext_def_id_str(tcx, def_id, "_threadlocal", args),
                ty::InstanceKind::FutureDropPollShim(def_id, _proxy_cor_ty, _impl_cor_ty) =>
                    ext_def_id_str(tcx, def_id, "_futuredroppoll", args),
                ty::InstanceKind::FnPtrAddrShim(def_id, _ty) =>
                    ext_def_id_str(tcx, def_id, "_fnptraddr", args),
                ty::InstanceKind::AsyncDropGlueCtorShim(def_id, _ty) =>
                    ext_def_id_str(tcx, def_id, "_asyncdropgluector", args),
                ty::InstanceKind::AsyncDropGlue(def_id, _ty) =>
                    ext_def_id_str(tcx, def_id, "_asyncdropglue", args),
            }
        },
        FnInst::ClosureFnPointer(base_inst) => {
            format!("{}::_closurefnptr", inst_id_str(tcx, base_inst))
        },
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

pub fn vtable_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> String {
    ext_def_id_str(mir.tcx, trait_ref.def_id(), "_vtbl", trait_ref)
}

/// Get the mangled name of a monomorphic function.  As a side effect, this marks the function as
/// "used", so its body will be emitted too.
pub fn get_fn_def_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    defid: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> String {
    let inst = ty::Instance::try_resolve(
        mir.tcx,
        ty::TypingEnv::fully_monomorphized(),
        defid,
        args,
    );

    // Compute the mangled name of the monomorphized instance being called.
    if let Ok(Some(inst)) = inst {
        mir.used.instances.insert(inst.into());
        inst_id_str(mir.tcx, inst)
    } else {
        eprintln!(
            "error: failed to resolve FnDef Instance: {:?}, {:?}",
            defid, args,
        );
        def_id_str(mir.tcx, defid)
    }
}

pub fn get_drop_fn_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<String> {
    let inst = ty::Instance::resolve_drop_in_place(mir.tcx, ty);
    if let ty::InstanceKind::DropGlue(_, None) = inst.def {
        // `None` instead of a `Ty` indicates this drop glue is a no-op.
        return None;
    }
    mir.used.instances.insert(inst.into());
    Some(inst_id_str(mir.tcx, inst))
}

impl ToJson<'_> for hir::def_id::DefId {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        json!(def_id_str(mir.tcx, *self))
    }
}

/// rustc's vtables have null entries for non-object-safe methods (those with `Where Self: Sized`).
/// We omit such methods from our vtables.  This function adjusts vtable indices from rustc's way
/// of counting to ours.
///
/// This function also accounts for the extra `drop_in_place` method that we
/// include in traits/vtables in `analyz::{emit_trait,build_vtable_items}`.
fn adjust_method_index<'tcx>(
    tcx: TyCtxt<'tcx>,
    tref: ty::Binder<'tcx, ty::TraitRef<'tcx>>,
    raw_idx: usize,
) -> usize {
    let methods = tcx.vtable_entries(tcx.instantiate_bound_regions_with_erased(tref));
    methods.iter().take(raw_idx)
        .filter(|m| matches!(m, ty::vtable::VtblEntry::Method(_)))
        .count()
        // For the extra drop method
        + 1
}

impl<'tcx> ToJson<'tcx> for FnInst<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match *self {
            FnInst::Real(ty_inst) => ty_inst.to_json(mir),
            FnInst::ClosureFnPointer(ty_inst) => {
                mir.used.instances.insert(ty_inst.into());
                json!({
                    "kind": "ClosureFnPointerShim",
                    "call_mut": inst_id_str(mir.tcx, ty_inst),
                })
            },
        }
    }
}

impl<'tcx> ToJson<'tcx> for ty::Instance<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let args = mir.tcx.normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            self.args,
        );

        match self.def {
            ty::InstanceKind::Item(did) => json!({
                "kind": "Item",
                "def_id": did.to_json(mir),
                "args": args.to_json(mir),
            }),
            ty::InstanceKind::Intrinsic(did) => json!({
                "kind": "Intrinsic",
                "def_id": did.to_json(mir),
                "args": args.to_json(mir),
            }),
            ty::InstanceKind::VTableShim(did) => json!({
                "kind": "VTableShim",
                "def_id": did.to_json(mir),
                "args": args.to_json(mir),
            }),
            ty::InstanceKind::ReifyShim(did, _reason) => json!({
                "kind": "ReifyShim",
                "def_id": did.to_json(mir),
                "args": args.to_json(mir),
            }),
            ty::InstanceKind::FnPtrShim(did, ty) => json!({
                "kind": "FnPtrShim",
                "def_id": did.to_json(mir),
                "args": args.to_json(mir),
                "ty": ty.to_json(mir),
            }),
            ty::InstanceKind::Virtual(did, idx) => {
                let self_ty = args.types().next()
                    .unwrap_or_else(|| panic!("expected self type in args for {:?}", self));
                let preds = match *self_ty.kind() {
                    ty::TyKind::Dynamic(ref preds, _region, _dynkind) => preds,
                    _ => panic!("expected `dyn` self type, but got {:?}", self_ty),
                };
                let ex_tref = match preds.principal() {
                    Some(x) => x,
                    None => panic!("no principal trait for {:?}?", self_ty),
                };
                let tref = ex_tref.with_self_ty(mir.tcx, self_ty);

                let erased_tref = mir.tcx.instantiate_bound_regions_with_erased(tref);
                let ti = TraitInst::from_trait_ref(mir.tcx, erased_tref);
                let trait_name = trait_inst_id_str(mir.tcx, &ti);
                mir.used.traits.insert(ti);

                json!({
                    "kind": "Virtual",
                    "trait_id": trait_name,
                    "item_id": did.to_json(mir),
                    "index": adjust_method_index(mir.tcx, tref, idx),
                })
            },
            ty::InstanceKind::ClosureOnceShim { call_once, .. } => json!({
                "kind": "ClosureOnceShim",
                "call_once": call_once.to_json(mir),
                "args": args.to_json(mir),
            }),
            ty::InstanceKind::DropGlue(did, ty) => json!({
                "kind": "DropGlue",
                "def_id": did.to_json(mir),
                "args": args.to_json(mir),
                "ty": ty.to_json(mir),
            }),
            ty::InstanceKind::CloneShim(did, ty) => {
                // We try to keep the cases in this `match` expression in sync
                // with the cases in rustc's `build_clone_shim` function (see
                // https://doc.rust-lang.org/1.86.0/nightly-rustc/src/rustc_mir_transform/shim.rs.html#432-455).
                //
                // TODO(#196): We are currently missing a case for
                // TyKind::Coroutine. We should
                // add this case, taking inspiration from how
                // `build_clone_shim` handles them and making sure that we
                // encode enough information for crucible-mir to use.
                let sub_tys = match *ty.kind() {
                    ty::TyKind::Tuple(ts) => ts[..].to_owned(),
                    ty::TyKind::Closure(_closure_did, args) =>
                        args.as_closure().upvar_tys()[..].to_owned(),
                    ty::TyKind::CoroutineClosure(_coroutine_closure_did, args) =>
                        args.as_coroutine_closure().upvar_tys()[..].to_owned(),
                    ty::TyKind::FnPtr(..) => vec![],
                    ty::TyKind::FnDef(..) => vec![],
                    _ => {
                        eprintln!("warning: don't know how to build clone shim for {:?}", ty);
                        vec![]
                    },
                };
                let callees = sub_tys.into_iter()
                    .map(|ty| {
                        let inst = ty::Instance::try_resolve(
                            mir.tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            did,
                            mir.tcx.mk_args(&[ty.into()]),
                        ).unwrap_or_else(|_| {
                            panic!("failed to resolve instance: {:?}, {:?}", did, ty);
                        });
                        if let Some(inst) = inst {
                            // Add the callee to `used.insances`, so we'll emit code for it even if
                            // it's otherwise unused.  If `inst` is itself a `CloneShim`, its own
                            // callees will be visited when generating the "intrinsics" entry for
                            // `inst`.
                            mir.used.instances.insert(inst.clone().into());
                        }
                        inst.map(|i| inst_id_str(mir.tcx, i))
                    }).collect::<Vec<_>>();
                json!({
                    "kind": "CloneShim",
                    "def_id": did.to_json(mir),
                    "args": args.to_json(mir),
                    "ty": ty.to_json(mir),
                    "callees": callees.to_json(mir),
                })
            },
            ty::InstanceKind::ConstructCoroutineInClosureShim { .. } => json!({
                "kind": "Unsupported",
            }),
            ty::InstanceKind::ThreadLocalShim(_def_id) => json!({
                "kind": "Unsupported",
            }),
            ty::InstanceKind::FutureDropPollShim(_def_id, _proxy_cor_ty, _impl_cor_ty) => json!({
                "kind": "Unsupported",
            }),
            ty::InstanceKind::FnPtrAddrShim(_def_id, _ty) => json!({
                "kind": "Unsupported",
            }),
            ty::InstanceKind::AsyncDropGlueCtorShim(_def_id, _ty) => json!({
                "kind": "Unsupported",
            }),
            ty::InstanceKind::AsyncDropGlue(_def_id, _ty) => json!({
                "kind": "Unsupported",
            }),
        }
    }
}

// For type _references_. To translate ADT defintions, do it explicitly.
impl<'tcx> ToJson<'tcx> for ty::Ty<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let tcx = mir.tcx;

        // If this type has already been interned, just return its ID.
        if let Some(id) = mir.tys.ty_get(*self) {
            return json!(id);
        }

        // Otherwise, convert the type to JSON.
        let ty_j = match self.kind() {
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
                json!({
                    "kind": "Array",
                    "ty": t.to_json(mir),
                    "size": {
                        "ty": tcx.types.usize.to_json(mir),
                        "rendered": const_to_json_uninterned(mir, size),
                    },
                })
            }
            &ty::TyKind::Ref(ref _region, ref ty, ref mtbl) => {
                json!({
                    "kind": "Ref",
                    "ty": ty.to_json(mir),
                    "mutability": mtbl.to_json(mir)
                })
            }
            &ty::TyKind::RawPtr(ref ty, ref mtbl) => {
                json!({
                    "kind": "RawPtr",
                    "ty": ty.to_json(mir),
                    "mutability": mtbl.to_json(mir)
                })
            }
            &ty::TyKind::Adt(adtdef, args) => {
                let ai = AdtInst::new(adtdef, args);
                mir.used.types.insert(ai);
                json!({
                    "kind": "Adt",
                    "name": adt_inst_id_str(mir.tcx, ai),
                    "orig_def_id": adtdef.did().to_json(mir),
                    "args": args.to_json(mir),
                })
            }
            &ty::TyKind::FnDef(defid, ref args) => {
                let name = get_fn_def_name(mir, defid, args);
                json!({
                    "kind": "FnDef",
                    "defid": name,
                })
            }
            &ty::TyKind::Param(..) => unreachable!(
                "no TyKind::Param should remain after monomorphization"
            ),
            &ty::TyKind::Closure(_defid, ref args) => {
                json!({
                    "kind": "Closure",
                    "upvar_tys": args.as_closure().upvar_tys().to_json(mir),
                    // crucible-mir uses the same representation for closures as it does for
                    // tuples, so no additional information is needed.
                })
            }
            &ty::TyKind::CoroutineClosure(_defid, ref args) => {
                json!({
                    "kind": "CoroutineClosure",
                    "upvar_tys": args.as_coroutine_closure().upvar_tys().to_json(mir),
                    // crucible-mir uses the same representation for coroutine closures as it does
                    // for tuples, so no additional information is needed.
                })
            }
            &ty::TyKind::Dynamic(preds, _region, dynkind) => {
                match dynkind {
                    DynKind::Dyn => {
                        let ti = TraitInst::from_dynamic_predicates(mir.tcx, preds);
                        let trait_name = trait_inst_id_str(mir.tcx, &ti);
                        mir.used.traits.insert(ti);
                        json!({
                            "kind": "Dynamic",
                            "trait_id": trait_name,
                            "predicates": preds.iter().map(|p|{
                                let p = tcx.instantiate_bound_regions_with_erased(p);
                                p.to_json(mir)
                            }).collect::<Vec<_>>(),
                        })
                    },
                }
            }
            &ty::TyKind::Alias(ty::AliasTyKind::Projection, _) => unreachable!(
                "no TyKind::Alias with AliasTyKind Projection should remain after monomorphization"
            ),
            &ty::TyKind::FnPtr(ref sig_tys, ref hdr) => {
                json!({"kind": "FnPtr", "signature": sig_tys.with(*hdr).to_json(mir)})
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
            &ty::TyKind::Coroutine(defid, args) => {
                merge(json!({"kind": "Coroutine"}), coroutine_args(mir, defid, args))
            }
            &ty::TyKind::CoroutineWitness(_, _) => {
                // TODO
                json!({"kind": "CoroutineWitness"})
            }
            &ty::TyKind::Alias(ty::AliasTyKind::Opaque, _) => {
                // TODO
                json!({"kind": "Alias"})
            }
            &ty::TyKind::Pat(_, _) => {
                json!({"kind": "Unsupported"})
            },
            &ty::TyKind::UnsafeBinder(_unsafe_binder_inner) => {
                json!({"kind": "Unsupported"})
            },
            &ty::TyKind::Alias(_alias_ty_kind, _alias_ty) => {
                json!({"kind": "Unsupported"})
            },
        };

        // Get layout information.
        let layout_j =
          match self.kind() {
            // `CoroutineWitness` should not appear in actual code, so we
            // can't compute their layout---and we don't need it---so we just
            // skip it.
            &ty::TyKind::CoroutineWitness(_,_) => None,
            _ => {
              let layout = tcx
                .layout_of(
                    ty::TypingEnv::fully_monomorphized().as_query_input(*self)
                )
                .unwrap_or_else(|e| {
                    panic!("failed to get layout of {:?}: {}", self, e)
                });
                if layout.is_sized() {
                    Some(json!({
                        "align": layout.align.abi.bytes(),
                        "size": layout.size.bytes()
                }))
                } else {
                    None
                }
            }
        };

        let needs_drop = self.needs_drop(tcx, ty::TypingEnv::fully_monomorphized());

        // Add the new entry to the interning table.
        let id = mir.tys.ty_insert(tcx, *self, ty_j, layout_j, needs_drop);
        json!(id)
    }
}

pub fn coroutine_args<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    defid: DefId,
    args: ty::GenericArgsRef<'tcx>,
) -> serde_json::Value {
    let tcx = mir.tcx;
    let co_args = args.as_coroutine();
    let co_layout = tcx.coroutine_layout(defid, args).unwrap();
    let co_layout = tcx.instantiate_and_normalize_erasing_regions(
        args,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(co_layout.clone()),
    );
    json!({
        // Discriminant, upvar, and saved-local types
        "discr_ty": co_args.discr_ty(tcx).to_json(mir),
        "upvar_tys": co_args.upvar_tys().to_json(mir),
        "saved_tys": co_layout.field_tys.iter().map(|cst| {
            cst.ty.to_json(mir)
        }).collect::<Vec<_>>(),
        // Mapping of variant and field index to `saved_tys` index.
        "field_map": co_layout.variant_fields.iter().map(|fields| {
            fields.iter().map(|csl| {
                csl.as_usize()
            }).collect::<Vec<_>>()
        }).collect::<Vec<_>>(),
    })
}

impl ToJson<'_> for ty::ParamTy {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(self.index)
    }
}

impl<'tcx> ToJson<'tcx> for ty::PolyFnSig<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let sig = ms.tcx.instantiate_bound_regions_with_erased(*self);
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
            "args":  self.args.to_json(ms)
        })
    }
}

impl<'tcx> ToJson<'tcx> for ty::AliasTerm<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "args": self.args.to_json(ms),
            "def_id": self.def_id.to_json(ms)
        })
    }
}

// Clause (static / `where` clause)

impl<'tcx> ToJson<'tcx> for ty::Clause<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self.kind().skip_binder() {
            ty::ClauseKind::Trait(tp) => {
                json!({
                    "trait_pred": tp.trait_ref.to_json(ms)
                })
            }
            ty::ClauseKind::Projection(pp) => match pp.term.kind() {
                ty::TermKind::Ty(ty) => json!({
                    "projection_term": pp.projection_term.to_json(ms),
                    "ty": ty.to_json(ms),
                }),
                ty::TermKind::Const(_) => json!("unknown_const_projection"),
            }
            _ => {
                json!("unknown_clause")
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
                    "args": trait_ref.args.to_json(ms),
                })
            },
            &ty::ExistentialPredicate::Projection(ref proj) => match proj.term.kind() {
                ty::TermKind::Ty(ty) => json!({
                    "kind": "Projection",
                    "proj": proj.def_id.to_json(ms),
                    "args": proj.args.to_json(ms),
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
                let parent_preds = ms.tcx.predicates_of(parent_id);
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
                let parent_generics = ms.tcx.generics_of(parent_id);
                gather_params(ms, &parent_generics, dest);
            }
            dest.extend(generics.own_params.iter().map(|p| p.to_json(ms)));
        }

        let mut json_params: Vec<serde_json::Value> = Vec::new();
        gather_params(ms, self, &mut json_params);
        json!({
            "own_params": json_params
        }) // TODO
    }
}

pub trait ToJsonAg {
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> serde_json::Value;
}

impl<'tcx> ToJson<'tcx> for ty::GenericArg<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self.kind() {
            ty::GenericArgKind::Type(ref ty) => ty.to_json(mir),
            // Lifetimes and Consts aren't "types" in the sense that you cannot
            // have variables with these types, but they do nevertheless appear
            // in lists of type substitutions, so we need to handle them
            // somehow.
            //
            // For Consts, we emit an entry that contains the constant's
            // rendered value. This has no effect on the semantics of
            // crucible-mir. The only real purpose it serves is to allow SAW to
            // distinguish between different instantiations of polymorphic
            // functions or ADTs that use const generics.
            ty::GenericArgKind::Const(c) => const_to_json_interned(mir, &c),
            // Lifetimes are less interesting from a SAW perspective, as users
            // typically do not care about the exact region used to instantiate
            // lifetime-generic functions or ADTs. crucible-mir has a dummy
            // TyLifetime variant to represent lifetime instantiations. We emit
            // looks vaguely like an interned type's ID here, and handle it
            // specially in MIR.JSON.
            ty::GenericArgKind::Lifetime(_) => json!("nonty::Lifetime"),
        }
    }
}

use self::machine::RenderConstMachine;
mod machine {
    use std::borrow::Cow;
    use super::*;
    use rustc_const_eval::interpret::*;
    use rustc_data_structures::fx::FxIndexMap;
    use rustc_middle::ty::*;
    use rustc_middle::ty::layout::TyAndLayout;
    use rustc_abi::Size;
    use rustc_target::callconv::FnAbi;
    pub struct RenderConstMachine<'tcx> {
        stack: Vec<Frame<'tcx, CtfeProvenance, ()>>,
    }

    impl<'tcx> RenderConstMachine<'tcx> {
        pub fn new() -> RenderConstMachine<'tcx> {
            RenderConstMachine {
                stack: Vec::new()
            }
        }
    }

    impl<'tcx> Machine<'tcx> for RenderConstMachine<'tcx> {
        type MemoryKind = !;
        type Provenance = CtfeProvenance;
        type ProvenanceExtra = ();
        type ExtraFnVal = !;
        type FrameExtra = ();
        type AllocExtra = ();
        type Bytes = Box<[u8]>;
        type MemoryMap = FxIndexMap<
            AllocId,
            (MemoryKind<!>, Allocation),
        >;

        const GLOBAL_KIND: Option<Self::MemoryKind> = None;
        const PANIC_ON_ALLOC_FAIL: bool = false;

        fn enforce_alignment(_ecx: &InterpCx<'tcx, Self>) -> bool {
            false
        }

        #[inline(always)]
        fn ignore_optional_overflow_checks(_ecx: &InterpCx<'tcx, Self>) -> bool {
            true
        }

        fn enforce_validity(_ecx: &InterpCx<'tcx, Self>, _layout: TyAndLayout<'tcx>) -> bool {
            false
        }

        fn find_mir_or_eval_fn(
            _ecx: &mut InterpCx<'tcx, Self>,
            _instance: ty::Instance<'tcx>,
            _abi: &FnAbi<'tcx, Ty<'tcx>>,
            _args: &[FnArg<'tcx, Self::Provenance>],
            _destination: &PlaceTy<'tcx, Self::Provenance>,
            _target: Option<mir::BasicBlock>,
            _unwind: mir::UnwindAction,
        ) -> InterpResult<'tcx, Option<(&'tcx mir::Body<'tcx>, ty::Instance<'tcx>)>> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "find_mir_or_eval_fn".into(),
                ),
            )).into()
        }

        fn call_extra_fn(
            _ecx: &mut InterpCx<'tcx, Self>,
            _fn_val: Self::ExtraFnVal,
            _abi: &FnAbi<'tcx, Ty<'tcx>>,
            _args: &[FnArg<'tcx, Self::Provenance>],
            _destination: &PlaceTy<'tcx, Self::Provenance>,
            _target: Option<mir::BasicBlock>,
            _unwind: mir::UnwindAction,
        ) -> InterpResult<'tcx> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "call_extra_fn".into(),
                ),
            )).into()
        }

        fn call_intrinsic(
            _ecx: &mut InterpCx<'tcx, Self>,
            _instance: ty::Instance<'tcx>,
            _args: &[OpTy<'tcx, Self::Provenance>],
            _destination: &PlaceTy<'tcx, Self::Provenance>,
            _target: Option<mir::BasicBlock>,
            _unwind: mir::UnwindAction,
        ) -> InterpResult<'tcx, Option<Instance<'tcx>>> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "call_intrinsic".into(),
                ),
            )).into()
        }

        fn check_fn_target_features(
            _ecx: &InterpCx<'tcx, Self>,
            _instance: ty::Instance<'tcx>,
        ) -> InterpResult<'tcx> {
            interp_ok(())
        }

        fn assert_panic(
            _ecx: &mut InterpCx<'tcx, Self>,
            _msg: &mir::AssertMessage<'tcx>,
            _unwind: mir::UnwindAction,
        ) -> InterpResult<'tcx> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "assert_panic".into(),
                ),
            )).into()
        }

        fn panic_nounwind(_ecx: &mut InterpCx<'tcx, Self>, _msg: &str) -> InterpResult<'tcx> {
            unreachable!("rustc typechecked code should not reach this point")
        }

        fn unwind_terminate(
            _ecx: &mut InterpCx<'tcx, Self>,
            _reason: mir::UnwindTerminateReason,
        ) -> InterpResult<'tcx> {
            unreachable!("rustc typechecked code should not reach this point")
        }

        fn binary_ptr_op(
            _ecx: &InterpCx<'tcx, Self>,
            _bin_op: mir::BinOp,
            _left: &ImmTy<'tcx, Self::Provenance>,
            _right: &ImmTy<'tcx, Self::Provenance>,
        ) -> InterpResult<'tcx, ImmTy<'tcx, Self::Provenance>> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "binary_ptr_op".into(),
                ),
            )).into()
        }

        fn ub_checks(_ecx: &InterpCx<'tcx, Self>) -> InterpResult<'tcx, bool> {
            interp_ok(false)
        }

        fn contract_checks(_ecx: &InterpCx<'tcx, Self>) -> InterpResult<'tcx, bool> {
            interp_ok(false)
        }

        fn extern_static_pointer(
            _ecx: &InterpCx<'tcx, Self>,
            _def_id: DefId,
        ) -> InterpResult<'tcx, Pointer<Self::Provenance>> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "extern_static_base_pointer".into(),
                ),
            )).into()
        }

        fn ptr_from_addr_cast(
            _ecx: &InterpCx<'tcx, Self>,
            _addr: u64,
        ) -> InterpResult<'tcx, Pointer<Option<Self::Provenance>>> {
            unimplemented!("ptr_from_addr_cast")
        }

        fn expose_provenance(
            _ecx: &InterpCx<'tcx, Self>,
            _ptr: Self::Provenance,
        ) -> InterpResult<'tcx> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "expose_ptr".into(),
                ),
            )).into()
        }

        fn ptr_get_alloc(
            _ecx: &InterpCx<'tcx, Self>,
            ptr: Pointer<Self::Provenance>,
            _size: i64
        ) -> Option<(AllocId, Size, Self::ProvenanceExtra)> {
            let (prov, offset) = ptr.prov_and_relative_offset();
            Some((prov.alloc_id(), offset, ()))
        }

        fn adjust_global_allocation<'b>(
            _ecx: &InterpCx<'tcx, Self>,
            _id: AllocId,
            alloc: &'b Allocation,
        ) -> InterpResult<'tcx, Cow<'b, Allocation<Self::Provenance, Self::AllocExtra>>> {
            interp_ok(Cow::Borrowed(alloc))
        }

        fn init_local_allocation(
            _ecx: &InterpCx<'tcx, Self>,
            _id: AllocId,
            _kind: MemoryKind<Self::MemoryKind>,
            _size: Size,
            _align: Align,
        ) -> InterpResult<'tcx, Self::AllocExtra> {
            interp_ok(())
        }

        fn adjust_alloc_root_pointer(
            _ecx: &InterpCx<'tcx, Self>,
            ptr: Pointer,
            _kind: Option<MemoryKind<Self::MemoryKind>>,
        ) -> InterpResult<'tcx, Pointer<Self::Provenance>> {
            interp_ok(ptr)
        }

        fn init_frame(
            _ecx: &mut InterpCx<'tcx, Self>,
            _frame: Frame<'tcx, Self::Provenance>,
        ) -> InterpResult<'tcx, Frame<'tcx, Self::Provenance, Self::FrameExtra>> {
            Err(InterpErrorKind::Unsupported(
                UnsupportedOpInfo::Unsupported(
                    "init_frame_extra".into(),
                ),
            )).into()
        }

        fn stack<'a>(
            ecx: &'a InterpCx<'tcx, Self>,
        ) -> &'a [Frame<'tcx, Self::Provenance, Self::FrameExtra>] {
            &ecx.machine.stack
            // unimplemented!("stack")
        }

        fn stack_mut<'a>(
            _ecx: &'a mut InterpCx<'tcx, Self>,
        ) -> &'a mut Vec<Frame<'tcx, Self::Provenance, Self::FrameExtra>> {
            unimplemented!("stack_mut")
        }

        fn get_global_alloc_salt(
            _ecx: &InterpCx<'tcx, Self>,
            _instance: Option<ty::Instance<'tcx>>,
        ) -> usize {
            mir::interpret::CTFE_ALLOC_SALT
        }

        fn get_default_alloc_params(&self) -> <Self::Bytes as AllocBytes>::AllocParams {
        }
    }
}

/// Serialize a `ty::Const` to JSON, representing it as an interned type. This
/// is used to serialize instantiations of const generic parameters. (See
/// `const_to_json_uninterned` for a variant of this function that does not
/// perform interning.)
fn const_to_json_interned<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    c: &ty::Const<'tcx>,
) -> serde_json::Value {
    // If this constant has already been interned, just return its ID.
    if let Some(id) = mir.tys.const_get(*c) {
        return json!(id);
    }

    let c_j = json!({
        "kind": "Const",
        "constant": const_to_json_uninterned(mir, c),
    });

    // Add the new entry to the interning table.
    let id = mir.tys.const_insert(mir.tcx, *c, c_j);
    json!(id)
}

/// Serialize a `ty::Const` to JSON without interning it. This is used to
/// serialize the sizes of array types, as well as value-level constants. It is
/// also one step of the process used to serialize instantiations of const
/// generic parameters. (See `const_to_json_interned` for the function that
/// adds interning on top of this.)
fn const_to_json_uninterned<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    c: &ty::Const<'tcx>,
) -> serde_json::Value {
    // This assumes the use of ConstKind::Value. This assumption appears to
    // hold for all ty::Consts that we serialize to JSON at the moment. It is
    // conceivable that we might encounter a different variant (e.g.,
    // ConstKind::Unevaluated) some day, however. If we do, we will need to
    // rethink this approach.
    if let ty::ConstKind::Value(cv) = c.kind() {
        let const_val = mir.tcx.valtree_to_const_val(cv);
        return (const_val, cv.ty).to_json(mir)
    }
    panic!("don't know how to translate ConstKind::{:?}", c.kind())
}

// This impl handles both type-level constants (namely, the sizes of array
// types and instantiations of const generic parameters) as well as value-level
// constants (e.g., the payload of a ConstOperand). At present, we only intern
// type-level constants. See the implementation of the ToJson impl for
// ty::Const for how interning is implemented.
impl<'tcx> ToJson<'tcx> for (mir::ConstValue, ty::Ty<'tcx>) {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let (val, ty) = *self;
        let mut icx = interpret::InterpCx::new(
            mir.tcx,
            DUMMY_SP,
            ty::TypingEnv::fully_monomorphized(),
            RenderConstMachine::new(),
        );
        let op_ty = as_opty(mir.tcx, &mut icx, val, ty);

        render_opty(mir, &mut icx, &op_ty)
    }
}

pub fn get_const_usize<'tcx>(tcx: ty::TyCtxt<'tcx>, c: ty::Const<'tcx>) -> usize {
    if let ty::ConstKind::Value(cv) = c.kind() {
        if let ty::ValTreeKind::Leaf(val) = *cv.valtree {
            let v = val.to_target_usize(tcx);
            return v as usize
        }
    }
    panic!("don't know how to translate ConstKind::{:?}", c.kind())
}

pub fn render_opty<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
    op_ty: &interpret::OpTy<'tcx>,
) -> serde_json::Value {
    try_render_opty(mir, icx, op_ty).unwrap_or_else(|| {
        json!({
            "kind": "unsupported_const",
            "debug_val": format!("{:?}", op_ty),
        })
    })
}

pub fn try_render_opty<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
    op_ty: &interpret::OpTy<'tcx>,
) -> Option<serde_json::Value> {
    let ty = op_ty.layout.ty;
    let layout = op_ty.layout.layout;
    let tcx = mir.tcx;

    Some(match *ty.kind() {
        ty::TyKind::Bool |
        ty::TyKind::Char |
        ty::TyKind::Uint(_) =>
        {
            let s = icx.read_immediate(op_ty).unwrap().to_scalar();
            let size = layout.size();
            let bits = s.to_bits(size).unwrap();

            json!({
                "kind": match *ty.kind() {
                    ty::TyKind::Bool => "bool",
                    ty::TyKind::Char => "char",
                    ty::TyKind::Uint(ty::UintTy::Usize) => "usize",
                    ty::TyKind::Uint(_) => "uint",
                    _ => unreachable!(),
                },
                "size": size.bytes(),
                "val": bits.to_string(),
            })
        }
        ty::TyKind::Int(_i) => {
            let s = icx.read_immediate(op_ty).unwrap().to_scalar();
            let size = layout.size();
            let bits = s.to_bits(size).unwrap();
            let mut val = bits as i128;
            if bits & (1 << (size.bits() - 1)) != 0 && size.bits() < 128 {
                // Sign-extend to 128 bits
                val |= -1_i128 << size.bits();
            }

            json!({
                "kind": match *ty.kind() {
                    ty::TyKind::Int(ty::IntTy::Isize) => "isize",
                    ty::TyKind::Int(_) => "int",
                    _ => unreachable!(),
                },
                "size": size.bytes(),
                "val": val.to_string(),
            })
        }
        ty::TyKind::Float(fty) => {
            let s = icx.read_immediate(op_ty).unwrap().to_scalar();
            let size = layout.size();
            let val_str = match fty {
                ty::FloatTy::F16 => s.to_f16().unwrap().to_string(),
                ty::FloatTy::F32 => s.to_f32().unwrap().to_string(),
                ty::FloatTy::F64 => s.to_f64().unwrap().to_string(),
                ty::FloatTy::F128 => s.to_f128().unwrap().to_string(),
            };

            json!({
                "kind": "float",
                "size": size.bytes(),
                "val": val_str,
            })
        }
        ty::TyKind::Adt(adt_def, _args) => match adt_def.adt_kind() {
            ty::AdtKind::Struct => {
                let variant = adt_def.non_enum_variant();
                let mut field_vals = Vec::new();
                for field_idx in variant.fields.indices() {
                    let field = icx.project_field(op_ty, field_idx).unwrap();
                    field_vals.push(try_render_opty(mir, icx, &field)?)
                }

                let val: serde_json::Value = field_vals.into();

                json!({
                    "kind": "struct",
                    "fields": val,
                })
            },
            ty::AdtKind::Enum => {
                // Uninhabited enums cannot be constructed in source Rust, but
                // zero-sized constants that have uninhabited enum types can
                // appear in Rust code as an optimization. As such, we must
                // reckon with them here. We represent them with "zst", which
                // is the same treatment that we give to FnDef and Never types.
                if op_ty.layout.is_uninhabited() {
                    json!({"kind": "zst"})
                } else {
                    // We uphold `read_discriminant`'s precondition that the
                    // enum must be inhabited via the `is_uninhabited` check
                    // above.
                    let variant_idx = icx.read_discriminant(op_ty).unwrap();
                    let val = icx.project_downcast(op_ty, variant_idx).unwrap();
                    let mut field_vals = Vec::with_capacity(val.layout.fields.count());
                    for idx in 0 .. val.layout.fields.count() {
                        let field_opty =
                            icx.project_field(&val, FieldIdx::from_usize(idx)).unwrap();
                        field_vals.push(try_render_opty(mir, icx,  &field_opty)?);
                    }

                    json!({
                        "kind": "enum",
                        "variant": variant_idx.as_u32(),
                        "fields": field_vals,
                    })
                }
            },
            ty::AdtKind::Union => {
                json!({"kind": "union"})
            },
        },

        ty::TyKind::Foreign(_) => todo!("foreign is unimplemented"), // can't do this
        ty::TyKind::Str => unreachable!("str type should not occur here"),
        ty::TyKind::Array(ety, sz) => {
            let sz = get_const_usize(tcx, sz);
            let mut vals = Vec::with_capacity(sz);
            let mut iter = icx.project_array_fields(op_ty).unwrap();
            while let Some((_, field)) = iter.next(icx).unwrap() {
                let f_json = try_render_opty(mir, icx, &field);
                vals.push(f_json);
            }

            json!({
                "kind": "array",
                "element_ty": ety.to_json(mir),
                "elements": vals
            })

        }
        ty::TyKind::Slice(_) => unreachable!("slice type should not occur here"),

        // similar to ref in some ways
        ty::TyKind::RawPtr(_, mutability) =>
            try_render_ref_opty(mir, icx, op_ty, mutability)?,

        ty::TyKind::Ref(_, _, mutability) =>
            try_render_ref_opty(mir, icx, op_ty, mutability)?,

        ty::TyKind::FnDef(_, _) |
        ty::TyKind::Never => json!({"kind": "zst"}),

        ty::TyKind::FnPtr(_sig_tys, _hdr) => {
            let ptr = icx.read_pointer(op_ty).unwrap();
            let alloc = tcx.try_get_global_alloc(ptr.provenance?.alloc_id())?;
            match alloc {
                interpret::GlobalAlloc::Function { instance } => {
                    let expected_abi = ty.fn_sig(tcx).abi();
                    let real_abi = instance.ty(tcx, ty::TypingEnv::fully_monomorphized())
                        .fn_sig(tcx).abi();
                    // The implementation of `ClosureFnPointer` in `rustc_const_eval` simply
                    // produces a pointer to the closure's `call_once` function.  This means the
                    // result actually has the wrong ABI (I think there are some details of the ABI
                    // lowering that makes this work out).  When we detect this situation, we emit
                    // a pointer to a `ClosureFnPointer` shim instead.
                    let use_closure_shim =
                        expected_abi == ExternAbi::Rust && real_abi == ExternAbi::RustCall;
                    let instance = if use_closure_shim {
                        FnInst::ClosureFnPointer(instance)
                    } else {
                        FnInst::from(instance)
                    };
                    mir.used.instances.insert(instance);
                    json!({
                        "kind": "fn_ptr",
                        "def_id": inst_id_str(tcx, instance),
                    })
                },
                _ => unreachable!("Function pointer doesn't point to a function"),
            }
        }
        ty::TyKind::Dynamic(_, _, _) => unreachable!("dynamic should not occur here"),

        ty::TyKind::Closure(_defid, args) => {
            let upvars_count = args.as_closure().upvar_tys().len();
            let upvar_vals = try_render_opty_upvars(mir, icx, op_ty, upvars_count)?;
            json!({
                "kind": "closure",
                "upvars": upvar_vals,
            })
        }
        ty::TyKind::CoroutineClosure(_defid, args) => {
            let upvars_count = args.as_coroutine_closure().upvar_tys().len();
            let upvar_vals = try_render_opty_upvars(mir, icx, op_ty, upvars_count)?;
            json!({
                "kind": "coroutine_closure",
                "upvars": upvar_vals,
            })
        }
        ty::TyKind::Coroutine(_, _) => todo!("coroutine not supported yet"), // not supported in haskell
        ty::TyKind::CoroutineWitness(_, _) => todo!("coroutinewitness not supported yet"), // not supported in haskell

        ty::TyKind::Tuple(elts) => {
            let mut vals = Vec::with_capacity(elts.len());
            for i in 0..elts.len() {
                let fld: interpret::OpTy<'tcx> =
                    icx.project_field(op_ty, FieldIdx::from_usize(i)).unwrap();
                vals.push(render_opty(mir, icx, &fld));
            }
            json!({
                "kind": "tuple",
                "elements": vals
            })
        }

        // should go away during monomorphiszation but could in theory be resolvable to a real type
        ty::TyKind::Alias(_, _) => unreachable!("alias should not occur after monomorphization"),
        ty::TyKind::Param(_) => unreachable!("param should not occur after monomorphization"),

        ty::TyKind::Bound(_, _) => unreachable!("bound is not a real type?"),
        ty::TyKind::Placeholder(_) => unreachable!("placeholder is not a real type?"),
        ty::TyKind::Infer(_) => unreachable!("infer is not a real type?"),
        ty::TyKind::Error(_) => unreachable!("error is not a real type?"),

        ty::TyKind::Pat(_, _) => {
            json!({"kind": "unsupported"})
        },
        ty::TyKind::UnsafeBinder(_unsafe_binder_inner) => {
            json!({"kind": "unsupported"})
        },
    })
}

fn try_render_opty_upvars<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
    op_ty: &interpret::OpTy<'tcx>,
    upvars_count: usize,
) -> Option<Vec<serde_json::Value>> {
    let mut upvar_vals = Vec::with_capacity(upvars_count);
    for idx in 0 .. upvars_count {
        let upvar_opty =
            icx.project_field(op_ty, FieldIdx::from_usize(idx)).unwrap();
        upvar_vals.push(try_render_opty(mir, icx, &upvar_opty)?);
    }
    Some(upvar_vals)
}

fn make_allocation_body<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
    d: &MPlaceTy<'tcx>,
    is_mut: bool,
) -> serde_json::Value {
    fn do_default<'tcx>(
        mir: &mut MirState<'_, 'tcx>,
        icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
        d: &MPlaceTy<'tcx>,
    ) -> (ty::Ty<'tcx>, Option<serde_json::Value>) {
        let dty = d.layout.ty;
        let rlayout = mir.tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(dty)).unwrap();
        let mpty: MPlaceTy = d.offset_with_meta(Size::ZERO, OffsetMode::Inbounds, d.meta(), rlayout, icx).unwrap();
        let rendered = try_render_opty(mir, icx, &mpty.into());
        (dty, rendered)
    }

    let (ty, rendered) = if !is_mut {
        /// Common logic for emitting `"kind": "strbody"` constants, shared by the `str` and `CStr`
        /// cases.
        fn do_strbody<'tcx>(
            mir: &mut MirState<'_, 'tcx>,
            icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
            d: &MPlaceTy<'tcx>,
            len: u64,
        ) -> (ty::Ty<'tcx>, Option<serde_json::Value>) {
            let tcx = mir.tcx;
            let mem = icx
                .read_bytes_ptr_strip_provenance(d.ptr(), Size::from_bytes(len))
                .unwrap();
            // corresponding array type for contents
            let elem_ty = tcx.mk_ty_from_kind(ty::TyKind::Uint(ty::UintTy::U8));
            let aty = ty::Ty::new_array(tcx, elem_ty, len);
            let rendered = json!({
                "kind": "strbody",
                "elements": mem,
                "len": len
            });
            (aty, Some(rendered))
        }

        // Special cases for references to unsized types. Currently, the
        // following are supported:
        //
        // * String slices (&str and &CStr)
        // * Array slices (&[T])
        // * Trait objects (&dyn Trait)
        // * Custom dynamically sized types, i.e., structs where the last field
        //   is an unsized type
        //
        // These special cases and the ones in try_render_ref_opty below should
        // be kept in sync.
        fn do_unsized<'tcx>(
            mir: &mut MirState<'_, 'tcx>,
            icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
            d: &MPlaceTy<'tcx>,
        ) -> (ty::Ty<'tcx>, Option<serde_json::Value>) {
            let tcx = mir.tcx;
            let dty = d.layout.ty;

            match dty.kind() {
                ty::TyKind::Str => {
                    let len = d.len(icx).unwrap();
                    do_strbody(mir, icx, d, len)
                },
                ty::TyKind::Adt(adt_def, _) if tcx.is_lang_item(adt_def.did(), LangItem::CStr) => {
                    // `<MPlaceTy as Projectable>::len` asserts that the input must have `Slice` or
                    // `Str` type.  However, the implementation it uses works fine on `CStr` too, so we
                    // copy-paste the code here.
                    let len = d.meta().unwrap_meta().to_target_usize(icx).unwrap();
                    do_strbody(mir, icx, d, len)
                },
                ty::TyKind::Slice(slice_ty) => {
                    let slice_len = d.len(icx).unwrap();
                    let mut elt_values = Vec::with_capacity(slice_len as usize);
                    for idx in 0..slice_len {
                        let elt = icx.project_index(&d.clone().into(), idx).unwrap();
                        elt_values.push(try_render_opty(mir, icx, &elt));
                    }
                    // corresponding array type for contents
                    let aty = ty::Ty::new_array(tcx, *slice_ty, slice_len);
                    let rendered = json!({
                        // this can now be the same as an ordinary array
                        "kind": "array",
                        "elements": elt_values,
                        "len": slice_len
                    });
                    (aty, Some(rendered))
                },
                ty::TyKind::Dynamic(ref preds, _, _) => {
                    let unpacked_d = unpack_dyn_place(icx, d, preds).unwrap();
                    do_default(mir, icx, &unpacked_d)
                },
                ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() && !d.layout.is_sized() => {
                    let variant = adt_def.non_enum_variant();
                    let mut field_indices = variant.fields.indices().peekable();
                    let mut field_vals = Vec::new();

                    while let Some(field_idx) = field_indices.next() {
                        let field = icx.project_field(d, field_idx).unwrap();
                        if field_indices.peek().is_none() {
                            let (_ty, rendered) = do_unsized(mir, icx, &field);
                            field_vals.push(rendered);
                        } else {
                            let rendered = try_render_opty(mir, icx, &field.into());
                            field_vals.push(rendered);
                        }
                    }

                    let val: serde_json::Value = field_vals.into();

                    let rendered = json!({
                        "kind": "struct",
                        "fields": val,
                    });
                    // TODO RGS: Using `dty` below is wrong. This will report a
                    // type like S<[u8]>, but we actually want the type of the
                    // backing allocation, which is something like S<[u8; 4]>.
                    (dty, Some(rendered))
                },
                _ => do_default(mir, icx, d)
            }
        }

        do_unsized(mir, icx, d)
    } else {
        do_default(mir, icx, d)
    };

    // Default case
    return json!({
        "kind": "constant",
        "mutable": false,
        "ty": ty.to_json(mir),
        "rendered": rendered,
    });
}

fn try_render_ref_opty<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
    op_ty: &interpret::OpTy<'tcx>,
    mutability: hir::Mutability,
) -> Option<serde_json::Value> {
    let tcx = mir.tcx;

    fn raw_ptr(offset: Size) -> Option<serde_json::Value> {
        Some(json!({
            "kind": "raw_ptr",
            "val": offset.bytes().to_string(),
        }))
    }

    // Special case for nullptr
    let val = icx.read_immediate(op_ty).unwrap();
    let mplace = icx.ref_to_mplace(&val).unwrap();
    let (prov, offset) = mplace.ptr().into_raw_parts();
    if prov.is_none() {
        assert!(!mplace.meta().has_meta(), "not expecting meta for nullptr");
        return raw_ptr(offset);
    }

    let d = icx.deref_pointer(op_ty).unwrap();
    let is_mut = mutability == hir::Mutability::Mut;

    let (prov, d_offset) = d.ptr().into_raw_parts();
    let alloc = tcx.try_get_global_alloc(prov?.alloc_id())?;

    let def_id_json = match alloc {
        interpret::GlobalAlloc::Static(def_id) =>
            def_id.to_json(mir),
        interpret::GlobalAlloc::Memory(ca) => {
            let ty = op_ty.layout.ty;
            let def_id_str = match mir.allocs.get(ca, ty) {
                Some(alloc_id) => alloc_id.to_owned(),
                None => {
                    // create the allocation
                    let body = make_allocation_body(mir, icx, &d, is_mut);
                    mir.allocs.insert(tcx, ca, ty, body)
                }
            };
            def_id_str.to_json(mir)
        }
        interpret::GlobalAlloc::TypeId {..} => {
            return raw_ptr(offset);
        }
        _ =>
            // Give up
            return None
    };

    // TODO(#241): Lift this restriction.
    assert!(d_offset == Size::ZERO, "cannot handle nonzero reference offsets");

    if !is_mut {
        fn do_slice<'tcx>(
            icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
            d: &MPlaceTy<'tcx>,
            def_id_json: &serde_json::Value,
        ) -> serde_json::Value {
            // `<MPlaceTy as Projectable>::len` asserts that the input must have `Slice` or
            // `Str` type.  However, the implementation it uses works fine on `CStr` too, so we
            // copy-paste the code here.
            let len = d.meta().unwrap_meta().to_target_usize(icx).unwrap();
            json!({
                "kind": "slice",
                "def_id": def_id_json,
                "len": len
            })
        }

        // Special cases for references to unsized types. Currently, the
        // following are supported:
        //
        // * String slices (&str and &CStr)
        // * Array slices (&[T])
        // * Trait objects (&dyn Trait)
        // * Custom dynamically sized types, i.e., structs where the last field
        //   is an unsized type
        //
        // These special cases and the ones in make_allocation_body above
        // should be kept in sync. If the type isn't one of the ones above,
        // this function will return None.
        fn do_unsized<'tcx>(
            mir: &mut MirState<'_, 'tcx>,
            icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
            d: &MPlaceTy<'tcx>,
            def_id_json: &serde_json::Value,
        ) -> Option<serde_json::Value> {
            let tcx = mir.tcx;

            match d.layout.ty.kind() {
                ty::TyKind::Str | ty::TyKind::Slice(_) =>
                    Some(do_slice(icx, d, def_id_json)),
                ty::TyKind::Adt(adt_def, _) if tcx.is_lang_item(adt_def.did(), LangItem::CStr) =>
                    Some(do_slice(icx, d, def_id_json)),
                ty::TyKind::Dynamic(ref preds, _, _) => {
                    let self_ty = unpack_dyn_ty(icx, d, preds).unwrap();
                    let vtable_desc = preds.principal().map(|pred| pred.with_self_ty(tcx, self_ty));
                    match vtable_desc {
                        Some(vtable_desc) => {
                            mir.used.vtables.insert(vtable_desc);
                            let ti = TraitInst::from_dynamic_predicates(tcx, preds);
                            Some(json!({
                                "kind": "trait_object",
                                "def_id": def_id_json,
                                "trait_id": trait_inst_id_str(tcx, &ti),
                                "vtable": vtable_name(mir, vtable_desc),
                            }))
                        },
                        None =>
                            // If there is no principal trait bound, then all of
                            // the trait bounds are auto traits. We do not
                            // currently support computing vtables for these sorts
                            // of trait objects (see #239).
                            Some(json!({
                                "kind": "unsupported",
                            }))
                    }
                }
                ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() && !d.layout.is_sized() => {
                    let fields = &adt_def.non_enum_variant().fields;
                    let last_field_idx = fields.last_index()?;
                    let last_field_mpty = &icx.project_field(d, last_field_idx).unwrap();
                    do_unsized(mir, icx, last_field_mpty, def_id_json)
                },
                _ => None,
            }
        }

        match do_unsized(mir, icx, &d, &def_id_json) {
            Some(j) => return Some(j),
            None => (),
        }
    }

    return Some(json!({
        "kind": "static_ref",
        "def_id": def_id_json,
    }));
}

pub fn as_opty<'tcx>(
    tcx: TyCtxt<'tcx>,
    icx: &mut interpret::InterpCx<'tcx, RenderConstMachine<'tcx>>,
    cv: mir::ConstValue,
    ty: ty::Ty<'tcx>,
) -> interpret::OpTy<'tcx, interpret::CtfeProvenance> {
    use rustc_middle::mir::ConstValue;
    use rustc_const_eval::interpret::{CtfeProvenance, Pointer, Immediate, ImmTy};
    enum ImmediateOrIndirect {
        Immediate(Immediate),
        Indirect(Pointer<Option<CtfeProvenance>>),
    }
    let op = match cv {
        ConstValue::Indirect { alloc_id, offset } => {
            // We rely on mutability being set correctly in that allocation to prevent writes
            // where none should happen.
            let ptr = Pointer::new(CtfeProvenance::from(alloc_id), offset);
            ImmediateOrIndirect::Indirect(ptr.into())
        }
        ConstValue::Scalar(x) => ImmediateOrIndirect::Immediate(x.into()),
        ConstValue::ZeroSized => ImmediateOrIndirect::Immediate(Immediate::Uninit),
        ConstValue::Slice { alloc_id, meta } => {
            // We rely on mutability being set correctly in `data` to prevent writes
            // where none should happen.
            let ptr = Pointer::new(CtfeProvenance::from(alloc_id), Size::ZERO);
            ImmediateOrIndirect::Immediate(Immediate::new_slice(ptr.into(), meta, &tcx))
        }
    };

    let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty)).unwrap();

    match op {
        ImmediateOrIndirect::Immediate(imm) => ImmTy::from_immediate(imm, layout).into(),
        ImmediateOrIndirect::Indirect(ptr) => icx.ptr_to_mplace(ptr, layout).into(),
    }
}

fn iter_tojson<'a, 'tcx, I, V: 'a>(
    it: I,
    mir: &mut MirState<'_, 'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> serde_json::Value
where I: Iterator<Item = &'a V>, V: ToJsonAg {
    let mut j = Vec::with_capacity(it.size_hint().0);
    for v in it {
        j.push(v.tojson(mir, args));
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
        args: ty::GenericArgsRef<'tcx>,
    ) -> serde_json::Value {
        iter_tojson(self.iter(), mir, args)
    }
}

impl<T> ToJsonAg for Vec<T>
where
    T: ToJsonAg,
{
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> serde_json::Value {
        <[T] as ToJsonAg>::tojson(self, mir, args)
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
        args: ty::GenericArgsRef<'tcx>,
    ) -> serde_json::Value {
        iter_tojson(self.iter(), mir, args)
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
        let ty = ty::Ty::new_adt(mir.tcx, self.adt, self.args);
        let tyl = mir.tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
            .unwrap_or_else(|e| panic!("failed to get layout of {:?}: {}", ty, e));

        let kind = match self.adt.adt_kind() {
            AdtKind::Struct => json!({"kind": "Struct"}),
            AdtKind::Enum =>
                json!({
                    "kind": "Enum",
                    "discr_ty": self.adt
                                    .repr()
                                    .discr_type()
                                    .to_ty(mir.tcx)
                                    .to_json(mir)
                }),
            AdtKind::Union => json!({"kind": "Union"}),
        };

        let variants =
            if self.adt.is_enum() {
                render_enum_variants(mir, &self)
            } else {
                self.adt.variants()
                        .iter()
                        .map(|v| render_variant(mir, &self, v, &None))
                        .collect::<Vec<serde_json::Value>>()
                        .into()
            };

        json!({
            "name": adt_inst_id_str(mir.tcx, *self),
            "kind": kind,
            "variants": variants,
            "size": tyl.size.bytes(),
            "repr_transparent": self.adt.repr().transparent(),
            "orig_def_id": self.adt.did().to_json(mir),
            "orig_args": self.args.to_json(mir),
        })
    }
}

fn render_enum_variants<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    adt: &AdtInst<'tcx>,
) -> serde_json::Value {
    let mut variants = Vec::with_capacity(adt.adt.variants().len());
    for (idx, d_value) in adt.adt.discriminants(mir.tcx) {
        let v = adt.adt.variant(idx);
        let rendered = render_variant(mir, adt, v, &Some(d_value.to_string()));
        variants.push(rendered);
    }

    variants.into()
}

fn render_variant<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    adt: &AdtInst<'tcx>,
    v: &ty::VariantDef,
    mb_discr: &Option<String>
) -> serde_json::Value {
    let tcx = mir.tcx;
    let inhabited = v.inhabited_predicate(tcx, adt.adt)
                     .instantiate(tcx, adt.args)
                     .apply_ignore_module(tcx, ty::TypingEnv::fully_monomorphized());

    json!({
        "name": v.def_id.to_json(mir),
        "discr": v.discr.to_json(mir),
        "fields": v.fields.tojson(mir, adt.args),
        "ctor_kind": v.ctor_kind().to_json(mir),
        "discr_value": mb_discr,
        "inhabited": inhabited,
    })
}

impl ToJsonAg for ty::FieldDef {
    fn tojson<'tcx>(
        &self,
        mir: &mut MirState<'_, 'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> serde_json::Value {
        let unsubst_ty = mir.tcx.type_of(self.did);
        let ty = mir.tcx.instantiate_and_normalize_erasing_regions(
            args, ty::TypingEnv::fully_monomorphized(), unsubst_ty);
        json!({
            "name": self.did.to_json(mir),
            "ty": ty.to_json(mir),
        })
    }
}

pub fn handle_adt_ag<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    ak: &mir::AggregateKind<'tcx>,
    opv: &IndexVec<FieldIdx, mir::Operand<'tcx>>,
    ty: ty::Ty<'tcx>,
) -> serde_json::Value {
    match ak {
        &mir::AggregateKind::Adt(adt_did, variant, args, _, union_field_idx) => {
            let adt = mir.tcx.adt_def(adt_did);
            json!({
                "adt": AdtInst::new(adt, args).to_json(mir),
                "variant": variant.to_json(mir),
                "ops": opv.to_json(mir),
                "ty": ty.to_json(mir),
                "field": union_field_idx.to_json(mir),
            })
        }
        _ => unreachable!("bad"),
    }
}

// Based on `rustc_codegen_ssa::mir::FunctionCx::eval_mir_constant`
pub fn eval_mir_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &mir::ConstOperand<'tcx>,
) -> mir::ConstValue {
    constant.const_
        .eval(tcx, ty::TypingEnv::fully_monomorphized(), constant.span)
        .unwrap()
}

// Turn a place with a `dyn Trait` type into the actual dynamic type.
//
// This is based on the internals of
// `rustc_const_eval::interpret::InterpCx::unpack_dyn_trait`.
fn unpack_dyn_ty<'tcx>(
    icx: &InterpCx<'tcx, RenderConstMachine<'tcx>>,
    mplace: &MPlaceTy<'tcx>,
    expected_trait: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
) -> InterpResult<'tcx, ty::Ty<'tcx>> {
    assert!(
        matches!(mplace.layout.ty.kind(), ty::Dynamic(_, _, ty::Dyn)),
        "`unpack_dyn_ty` only makes sense on `dyn*` types"
    );
    let vtable = mplace.meta().unwrap_meta().to_pointer(icx)?;
    icx.get_ptr_vtable_ty(vtable, Some(expected_trait))
}

// Turn a place with a `dyn Trait` type into a place with the actual dynamic
// type.
//
// This is based on `rustc_const_eval::interpret::InterpCx::unpack_dyn_trait`.
fn unpack_dyn_place<'tcx>(
    icx: &InterpCx<'tcx, RenderConstMachine<'tcx>>,
    mplace: &MPlaceTy<'tcx>,
    expected_trait: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
) -> InterpResult<'tcx, MPlaceTy<'tcx>> {
    let ty = unpack_dyn_ty(icx, mplace, expected_trait)?;
    // This is a kind of transmute, from a place with unsized type and metadata to
    // a place with sized type and no metadata.
    let layout = icx.layout_of(ty)?;
    mplace.offset_with_meta(
        Size::ZERO,
        OffsetMode::Wrapping,
        MemPlaceMeta::None,
        layout,
        icx,
    )
}
