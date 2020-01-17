#![macro_use]

use rustc::ty::{self, TyCtxt, List, TyS};
use rustc::mir::{self, Body};
use rustc::hir;
use rustc::hir::def::DefKind;
use rustc::hir::def_id::{self, DefId, LOCAL_CRATE};
use rustc::mir::mono::MonoItem;
use rustc::session::config::OutputType;
use rustc::traits;
use rustc::ty::subst::Subst;
use rustc_codegen_utils;
use rustc_driver::source_name;
use rustc_interface::interface::Compiler;
use rustc_mir::monomorphize::collector::{self, MonoItemCollectionMode};
use rustc_target::spec::abi;
use syntax::symbol::Symbol;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;
use std::io;
use std::io::Write;
use std::fs::File;
use std::path::{Path, PathBuf};
use serde::ser::{Serialize, Serializer, SerializeSeq};
use serde_json;
use serde_cbor;

#[macro_use]
mod to_json;
mod ty_json;
use analyz::to_json::*;
use analyz::ty_json::*;
use lib_util::{self, JsonOutput, EntryKind};

basic_json_enum_impl!(mir::BinOp);

basic_json_enum_impl!(mir::NullOp);
basic_json_enum_impl!(mir::UnOp);

impl<'tcx> ToJson<'tcx> for ty::layout::VariantIdx {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        self.as_usize().into()
    }
}

impl<'tcx> ToJson<'tcx> for mir::Promoted {
    fn to_json(&self, _: &mut MirState) -> serde_json::Value {
        self.as_usize().into()
    }
}

impl<'tcx> ToJson<'tcx> for mir::AggregateKind<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::AggregateKind::Array(ty) => {
                json!({"kind": "Array", "ty": ty.to_json(mir)})
            }
            &mir::AggregateKind::Tuple => {
                json!({"kind": "Tuple"})
            }
            &mir::AggregateKind::Adt(_, _, _, _, _) => {
                panic!("adt should be handled upstream")
            }
            &mir::AggregateKind::Closure(ref defid, ref closuresubsts) => {
                json!({
                    "kind": "Closure",
                    "defid": defid.to_json(mir),
                    "closuresubsts": closuresubsts.substs.to_json(mir)
                })
            }
            &mir::AggregateKind::Generator(_, _, _,) => {
                // TODO
                json!({"kind": "Generator"})
            }
        }
    }
}

/// Compute the "vtable descriptor" for a given cast, if applicable.  We identify vtables by their
/// `PolyTraitRef`s, which uniquely determine the trait and self type, and which can be used by
/// downstream code such as `build_vtable`.
fn vtable_descriptor_for_cast<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    kind: mir::CastKind,
    old_ty: ty::Ty<'tcx>,
    new_ty: ty::Ty<'tcx>,
) -> Option<ty::PolyTraitRef<'tcx>> {
    let tcx = mir.state.tcx;

    if kind != mir::CastKind::Pointer(ty::adjustment::PointerCast::Unsize) {
        return None;
    }

    // Relevant code: rustc_codegen_ssa::base::unsized_info, and other functions in that file.
    let old_pointee = match old_ty.sty {
        ty::TyKind::Ref(_, ty, _) => ty,
        ty::TyKind::RawPtr(ref tm) => tm.ty,
        _ => return None,
    };
    let new_pointee = match new_ty.sty {
        ty::TyKind::Ref(_, ty, _) => ty,
        ty::TyKind::RawPtr(ref tm) => tm.ty,
        _ => return None,
    };

    if !tcx.is_sized_raw(ty::ParamEnv::reveal_all().and(old_pointee)) {
        // We produce a vtable only for sized -> TyDynamic casts.
        return None;
    }

    // Relevant code: rustc_codegen_ssa::meth::get_vtable
    let trait_ref = match new_pointee.sty {
        ty::TyKind::Dynamic(ref preds, _) =>
            preds.principal().map(|pred| pred.with_self_ty(tcx, old_pointee)),
        _ => return None,
    };
    let trait_ref: ty::PolyTraitRef = match trait_ref {
        Some(x) => x,
        // If there's no trait ref, it means the `Dynamic` predicates contain only auto traits.
        // The vtable for this trait object is empty.
        // TODO: handle this better (currently the output omits the "vtable" field)
        None => return None,
    };
    Some(trait_ref)
}

impl<'tcx> ToJson<'tcx> for mir::Rvalue<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::Rvalue::Use(ref op) => {
                json!({
                    "kind": "Use",
                    "usevar": op.to_json(mir)
                })
            }
            &mir::Rvalue::Repeat(ref op, s) => {
                json!({
                    "kind": "Repeat",
                    "op": op.to_json(mir),
                    "len": s
                })
            }
            &mir::Rvalue::Ref(_, ref bk, ref l) => {
                json!({
                    "kind": "Ref",
                    "region": "unimplement",
                    "borrowkind": bk.to_json(mir),
                    "refvar": l.to_json(mir)
                })
            } // UNUSED
            &mir::Rvalue::Len(ref l) => {
                json!({"kind": "Len", "lv": l.to_json(mir)})
            }
            &mir::Rvalue::Cast(ref ck, ref op, ref ty) => {
                let mut j = json!({
                    "kind": "Cast",
                    "type": ck.to_json(mir),
                    "op": op.to_json(mir),
                    "ty": ty.to_json(mir)
                });
                let op_ty = op.ty(mir.mir.unwrap(), mir.state.tcx);
                if let Some(vtable_desc) = vtable_descriptor_for_cast(mir, *ck, op_ty, ty) {
                    // On the Haskell side, the vtable is attached to the cast kind.
                    j["type"] = json!({
                        "kind": "UnsizeVtable",
                        "vtable": vtable_name(mir, vtable_desc),
                    });
                    mir.used.vtables.insert(vtable_desc);
                }
                j
            }
            &mir::Rvalue::BinaryOp(ref binop, ref op1, ref op2) => {
                json!({
                    "kind": "BinaryOp",
                    "op": binop.to_json(mir),
                    "L": op1.to_json(mir),
                    "R": op2.to_json(mir)
                })
            }
            &mir::Rvalue::CheckedBinaryOp(ref binop, ref op1, ref op2) => {
                json!({
                    "kind": "CheckedBinaryOp",
                    "op": binop.to_json(mir),
                    "L": op1.to_json(mir),
                    "R": op2.to_json(mir)
                })
            }
            &mir::Rvalue::NullaryOp(ref no, ref t) => {
                json!({
                    "kind": "NullaryOp",
                    "op": no.to_json(mir),
                    "ty": t.to_json(mir)
                })
            }
            &mir::Rvalue::UnaryOp(ref uo, ref o) => {
                json!({
                    "kind": "UnaryOp",
                    "uop": uo.to_json(mir),
                    "op": o.to_json(mir)
                })
            }
            &mir::Rvalue::Discriminant(ref lv) => {
                json!({"kind": "Discriminant", "val": lv.to_json(mir)})
            }
            &mir::Rvalue::Aggregate(ref ak, ref opv) => {
                if ty_json::is_adt_ak(ak) {
                    json!({
                        "kind": "AdtAg",
                        "ag": ty_json::handle_adt_ag (mir, ak, opv)
                    })
                } else {
                    json!({
                        "kind": "Aggregate",
                        "akind": ak.to_json(mir),
                        "ops": opv.to_json(mir)
                    })
                }
            }
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::Place<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(mir),
            "data" : self.projection.to_json(mir)
        })
    }
}

impl<'tcx> ToJson<'tcx> for mir::PlaceBase<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::PlaceBase::Local(ref l) => {
                json!({"kind": "Local", "localvar": local_json(ms, *l) })
            }
            &mir::PlaceBase::Static(ref s) => match s.kind {
                mir::StaticKind::Promoted(idx) => {
                    json!({
                        "kind": "Promoted",
                        "index": idx.to_json(ms),
                        "ty": s.ty.to_json(ms),
                    })
                },
                mir::StaticKind::Static(def_id) => {
                    json!({
                        "kind": "Static",
                        "def_id": def_id.to_json(ms),
                        "ty": s.ty.to_json(ms),
                    })
                },
            }
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::Projection<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(mir),
            "data" : self.elem.to_json(mir)
        })
    }
}

impl<'tcx> ToJson<'tcx> for mir::PlaceElem<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::ProjectionElem::Deref => {
                json!({"kind": "Deref"})
            }
            &mir::ProjectionElem::Field(ref f, ref ty) => {
                json!({
                    "kind": "Field",
                    "field": f.to_json(mir),
                    "ty": ty.to_json(mir)
                })
            }
            &mir::ProjectionElem::Index(ref op) => {
                json!({"kind": "Index", "op": local_json(mir, *op)})
            }
            &mir::ProjectionElem::ConstantIndex {
                ref offset,
                ref min_length,
                ref from_end,
            } => {
                json!({
                    "kind": "ConstantIndex",
                    "offset": offset,
                    "min_length": min_length,
                    "from_end": from_end
                })
            }
            &mir::ProjectionElem::Subslice { ref from, ref to } => {
                json!({"kind": "Subslice", "from": from, "to": to})
            }
            &mir::ProjectionElem::Downcast(ref _adt, ref variant) => {
                json!({"kind": "Downcast", "variant": variant.to_json(mir)})
            }
        }
    }
}

basic_json_impl!(mir::BasicBlock);

impl ToJson<'_> for mir::Field {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(self.index())
    }
}

basic_json_impl!(mir::AssertMessage<'a>, 'a);

impl<'tcx> ToJson<'tcx> for mir::Operand<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::Operand::Copy(ref l) => {
                json!({"kind": "Copy", "data": l.to_json(mir)})
            }
            &mir::Operand::Move(ref l) => {
                json!({"kind": "Move", "data": l.to_json(mir)})
            }
            &mir::Operand::Constant(ref l) => {
                json!({"kind": "Constant", "data": l.to_json(mir)})
            }
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::Constant<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "ty": self.ty.to_json(mir),
            "literal": self.literal.to_json(mir)
        })
    }
}

impl<'tcx> ToJson<'tcx> for mir::LocalDecl<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let pos = mir.state.session.source_map().span_to_string(self.source_info.span);
        json!({
            "mut": self.mutability.to_json(mir),
            "ty": self.ty.to_json(mir),
            // We specifically record whether the variable's type is zero-sized, because rustc
            // allows reading and taking refs of uninitialized zero-sized locals.
            "is_zst": mir.state.tcx.layout_of(ty::ParamEnv::reveal_all().and(self.ty))
                .expect("failed to get layout").is_zst(),
            "scope": format!("{:?}", self.source_info.scope),
            "pos": pos
        })
    }
}

impl<'tcx> ToJson<'tcx> for mir::Statement<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut j = match &self.kind {
            &mir::StatementKind::Assign(ref l, ref r) => {
                json!({
                    "kind": "Assign",
                    "lhs": l.to_json(mir),
                    "rhs": r.to_json(mir)
                })
            }
            &mir::StatementKind::FakeRead { .. } => {
                // TODO
                json!({"kind": "FakeRead"})
            }
            &mir::StatementKind::SetDiscriminant {
                ref place,
                ref variant_index,
            } => {
                json!({
                    "kind": "SetDiscriminant",
                    "lvalue": place.to_json(mir),
                    "variant_index": variant_index.to_json(mir)
                })
            }
            &mir::StatementKind::StorageLive(l) => {
                json!({"kind": "StorageLive", "slvar": local_json(mir, l)})
            }
            &mir::StatementKind::StorageDead(l) => {
                json!({"kind": "StorageDead", "sdvar": local_json(mir, l)})
            }
            &mir::StatementKind::InlineAsm { .. } => {
                // TODO
                json!({"kind": "InlineAsm"})
            }
            &mir::StatementKind::Retag { .. } => {
                // TODO
                json!({"kind": "Retag"})
            }
            &mir::StatementKind::AscribeUserType { .. } => {
                // TODO
                json!({"kind": "AscribeUserType"})
            }
            &mir::StatementKind::Nop => {
                json!({"kind": "Nop"})
            }
        };
        let pos = mir.state
                    .session
                    .source_map()
                    .span_to_string(self.source_info.span);
        j["pos"] = json!(pos);
        j
    }
}

impl<'tcx> ToJson<'tcx> for mir::TerminatorKind<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::TerminatorKind::Goto { ref target } => {
                json!({"kind": "Goto", "target": target.to_json(mir)})
            }
            &mir::TerminatorKind::SwitchInt {
                ref discr,
                ref switch_ty,
                ref values,
                ref targets,
            } => {
                let vals: Vec<String> =
                  values.iter().map(|&c| c.to_string()).collect();
                json!({
                    "kind": "SwitchInt",
                    "discr": discr.to_json(mir),
                    "switch_ty": switch_ty.to_json(mir),
                    "values": vals,
                    "targets": targets.to_json(mir)
                })
            }
            &mir::TerminatorKind::Resume => {
                json!({"kind": "Resume"})
            }
            &mir::TerminatorKind::Return => {
                json!({"kind": "Return"})
            }
            &mir::TerminatorKind::Unreachable => {
                json!({"kind": "Unreachable"})
            }
            &mir::TerminatorKind::Drop {
                ref location,
                ref target,
                ref unwind,
            } => {
                json!({
                    "kind": "Drop",
                    "location": location.to_json(mir),
                    "target" : target.to_json(mir),
                    "unwind": unwind.to_json(mir)
                })
            }
            &mir::TerminatorKind::DropAndReplace {
                ref location,
                ref value,
                ref target,
                ref unwind,
            } => {
                json!({
                    "kind": "DropAndReplace",
                    "location": location.to_json(mir),
                    "value": value.to_json(mir),
                    "target": target.to_json(mir),
                    "unwind": unwind.to_json(mir)
                })
            }
            &mir::TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ref cleanup,
                ref from_hir_call
            } => {
                json!({
                    "kind": "Call",
                    "func": func.to_json(mir),
                    "args": args.to_json(mir),
                    "destination": destination.to_json(mir),
                    "cleanup": cleanup.to_json(mir),
                    "from_hir_call": from_hir_call
                })
            }
            &mir::TerminatorKind::Assert {
                ref cond,
                ref expected,
                ref msg,
                ref target,
                ref cleanup,
            } => {
                json!({
                    "kind": "Assert",
                    "cond": cond.to_json(mir),
                    "expected": expected,
                    "msg": msg.to_json(mir),
                    "target": target.to_json(mir),
                    "cleanup": cleanup.to_json(mir)
                })
            }
            &mir::TerminatorKind::Abort => {
                json!({ "kind": "Abort" })
            }
            &mir::TerminatorKind::Yield { .. } => {
                // TODO
                json!({
                    "kind": "Yield"
                })
            }
            &mir::TerminatorKind::FalseEdges { .. } => {
                // TODO
                json!({
                    "kind": "FalseEdges"
                })
            }
            &mir::TerminatorKind::FalseUnwind { .. } => {
                // TODO
                json!({
                    "kind": "FalseUnwind"
                })
            }
            &mir::TerminatorKind::GeneratorDrop => {
                json!({ "kind": "GeneratorDrop" })
            }
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::BasicBlockData<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut sts = Vec::new();
        for statement in &self.statements {
            sts.push(statement.to_json(mir));
        }
        json!({
            "data": sts,
            "terminator": self.terminator().kind.to_json(mir)
        })
    }
}

fn local_json(ms: &mut MirState, local: mir::Local) -> serde_json::Value {
    let mut j = ms.mir.unwrap().local_decls[local].to_json(ms); // TODO
    let mut s = String::new();
    write!(&mut s, "{:?}", local).unwrap();
    j["name"] = json!(s);
    j
}

/// Serialize the MIR body `ms.mir` to JSON.
fn mir_body(
    ms: &mut MirState,
) -> serde_json::Value {
    let mir = ms.mir.unwrap();
    let mut vars = Vec::new();

    vars.push(local_json(ms, mir::RETURN_PLACE));
    for (_, v) in mir.vars_and_temps_iter().enumerate() {
        vars.push(local_json(ms, v));
    }

    let mut blocks = Vec::new();
    for bb in mir.basic_blocks().indices() {
        blocks.push(
            json!({
                "blockid": bb.to_json(ms),
                "block": mir[bb].to_json(ms)
            }),
        );
    }
    json!({
        "vars": vars,
        "blocks": blocks
    })
}


/// Workaround for a rustc bug.  MIR bodies are usually stored in normalized form, but for
/// associated constants whose types involve parameters, one occurrence of the constant type is not
/// substituted or normalized properly:
///
///     trait TheTrait {
///         const THE_CONST: Self;
///     }
///
///     impl TheTrait for u32 {
///         const THE_CONST: u32 = 123;
///     }
///
///
///     mir::Constant {
///         ty: u32,        // Substituted + normalized type of <u32 as TheTrait>::THE_CONST
///         literal: Const {
///             ty: Self,   // Unsubstituted declared type of THE_CONST.  This is the bug.
///             val: Unevaluated(
///                 the_crate::TheTrait::THE_CONST,
///                 [u32],  // Substs for TheTrait::THE_CONST
///             ),
///         },
///     }
///
/// This pass looks for Unevaluated constants, and copies the outer ty (which is computed
/// correctly) over top of the inner one.  Afterward, the MIR is well-formed and running `subst` on
/// it no longer panics.
fn subst_const_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    substs: ty::subst::SubstsRef<'tcx>,
    body: &mut Body<'tcx>,
) {
    mir::visit::MutVisitor::visit_body(
        &mut SubstConstTys { tcx, substs },
        body,
    );
    for promoted in body.promoted.iter_mut() {
        subst_const_tys(tcx, substs, promoted);
    }
}

struct SubstConstTys<'tcx> {
    tcx: TyCtxt<'tcx>,
    substs: ty::subst::SubstsRef<'tcx>,
}

impl<'tcx> mir::visit::MutVisitor<'tcx> for SubstConstTys<'tcx> {
    fn visit_constant(
        &mut self,
        constant: &mut mir::Constant<'tcx>,
        location: mir::Location,
    ) {
        if let mir::interpret::ConstValue::Unevaluated(..) = constant.literal.val {
            constant.literal = self.tcx.mk_const(ty::Const {
                ty: constant.ty,
                val: constant.literal.val,
            });
        }
        self.super_constant(constant, location);
    }
}



fn emit_trait<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    ti: TraitInst<'tcx>,
) -> io::Result<()> {
    let tcx = ms.state.tcx;
    let methods = tcx.vtable_methods(ty::Binder::dummy(ti.concrete_trait_ref(tcx)));
    let mut items = Vec::with_capacity(methods.len());
    for &m in methods {
        // `m` is `None` for methods with `where Self: Sized`.  We omit these from the vtable, and
        // adjust `InstanceDef::Virtual` indices accordingly.
        let (def_id, substs) = match m {
            Some(x) => x,
            None => continue,
        };
        let sig = tcx.subst_and_normalize_erasing_regions(
            substs, ty::ParamEnv::reveal_all(), &tcx.fn_sig(def_id));
        let sig = tcx.erase_late_bound_regions(&sig);

        items.push(json!({
            "kind": "Method",
            "item_id": def_id.to_json(ms),
            "signature": sig.to_json(ms),
            "generics": { "params": [] },
            "predicates": { "predicates": [] },
        }));
    }

    ms.state.session.note_without_error(&format!("Emitting trait def for {:?}", ti.dyn_ty(tcx)));

    out.emit(EntryKind::Trait, json!({
        // `name` corresponds to `trait_id` in vtables, Virtual, and Dynamic types.
        "name": trait_inst_id_str(ms.state.tcx, &ti),
        "items": items,
        "supertraits": [],
        "generics": { "params": [] },
        "predicates": { "predicates": [] },
    }))?;
    emit_new_types(ms, out)?;
    Ok(())
}

fn iter_trait_def_ids<'tcx>(
    state: &CompileState<'_, 'tcx>
) -> impl Iterator<Item=DefId> + 'tcx {
    let hir_map = state.tcx.hir();
    hir_map.krate().items.values()
        .filter(|it| match it.node {
            hir::ItemKind::Trait(..) => true,
            _ => false,
        })
        .map(|it| it.hir_id.owner_def_id())
}


/// Emit all statics defined in the current crate.
fn emit_statics(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let tcx = ms.state.tcx;
    let (mono_items, _) = collector::collect_crate_mono_items(tcx, MonoItemCollectionMode::Lazy);
    for mono_item in mono_items {
        match mono_item {
            MonoItem::Static(def_id) => emit_static(ms, out, def_id)?,
            MonoItem::Fn(_) |
            MonoItem::GlobalAsm(_) => {},
        }
    }
    Ok(())
}

fn emit_static(ms: &mut MirState, out: &mut impl JsonOutput, def_id: DefId) -> io::Result<()> {
    let tcx = ms.state.tcx;
    let name = def_id_str(tcx, def_id);
    let mir = tcx.optimized_mir(def_id);

    emit_fn(ms, out, &name, None, mir)?;
    emit_static_decl(ms, out, &name, mir.return_ty(), tcx.is_mutable_static(def_id), None)?;
    Ok(())
}

/// Add a new static declaration to `out.statics`.
fn emit_static_decl<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    name: &str,
    ty: ty::Ty<'tcx>,
    mutable: bool,
    promoted_info: Option<(&str, usize)>,
) -> io::Result<()> {
    let mut j = json!({
        "name": name,
        "ty": ty.to_json(ms),
        "mutable": mutable,
    });
    if let Some((parent, idx)) = promoted_info {
        j.as_object_mut().unwrap().insert("promoted_from".to_owned(), parent.into());
        j.as_object_mut().unwrap().insert("promoted_index".to_owned(), idx.into());
    }
    out.emit(EntryKind::Static, j)?;
    emit_new_types(ms, out)
}


fn has_test_attr(tcx: TyCtxt, def_id: DefId) -> bool {
    def_id.is_local() && tcx.has_attr(def_id, Symbol::intern("crux_test"))
}

/// Process the initial/root instances in the current crate.  This adds entries to `ms.used`, and
/// may also call `out.add_root` if this is a top-level crate.
fn init_instances(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let is_top_level = ms.state.session.parse_sess.config.iter()
        .any(|&(key, _)| key.as_str() == "crux_top_level");

    if is_top_level {
        init_instances_from_tests(ms, out)
    } else {
        init_instances_from_mono_items(ms)
    }
}

/// Add every `MonoItem::Fn` to `ms.used.instances`.
fn init_instances_from_mono_items(ms: &mut MirState) -> io::Result<()> {
    let tcx = ms.state.tcx;
    let (mono_items, _) = collector::collect_crate_mono_items(tcx, MonoItemCollectionMode::Lazy);
    for mono_item in mono_items {
        match mono_item {
            MonoItem::Fn(inst) => ms.used.instances.insert(inst),
            MonoItem::Static(_) |
            MonoItem::GlobalAsm(_) => {},
        }
    }
    Ok(())
}

/// Initialize the set of needed instances.  Returns a list of root instances.
fn init_instances_from_tests(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let tcx = ms.state.tcx;
    for &def_id in tcx.mir_keys(def_id::LOCAL_CRATE) {
        if !has_test_attr(tcx, def_id) {
            continue;
        }

        if tcx.def_kind(def_id) != Some(DefKind::Fn) {
            tcx.sess.span_err(
                tcx.def_span(def_id),
                "#[test] can only be applied to functions",
            );
            continue;
        }
        if tcx.generics_of(def_id).count() > 0 {
            tcx.sess.span_err(
                tcx.def_span(def_id),
                "#[test] cannot be applied to generic functions",
            );
            continue;
        }

        let inst = ty::Instance::resolve(tcx, ty::ParamEnv::reveal_all(), def_id, List::empty())
            .unwrap_or_else(|| {
                panic!("Instance::resolve failed to find test function {:?}?", def_id);
            });

        ms.used.instances.insert(inst);
        out.add_root(inst_id_str(tcx, inst))?;
    }
    Ok(())
}


/// Add a single `Instance` to `out.fns` and/or `out.intrinsics`, depending on its kind.
fn emit_instance<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    inst: ty::Instance<'tcx>,
) -> io::Result<()> {
    let tcx = ms.state.tcx;

    let name = inst_id_str(tcx, inst);

    // We actually record every instance in `intrinsics`, not just `InstanceDef::Intrinsic` and
    // other special functions, because the intrinsics table is used to look up CustomOps.
    // (CustomOps are keyed on the pre-monomorphization name of the function.)
    out.emit(EntryKind::Intrinsic, json!({
        "name": &name,
        "inst": inst.to_json(ms),
    }))?;
    emit_new_types(ms, out)?;

    let def_id = match inst.def {
        ty::InstanceDef::Item(def_id) => def_id,
        _ => return Ok(()),
    };

    // Foreign items and non-generics have no MIR available.
    if tcx.is_foreign_item(def_id) {
        return Ok(());
    }
    if !def_id.is_local() {
        if tcx.is_reachable_non_generic(def_id) {
            return Ok(());
        }
        // Items with upstream monomorphizations have already been translated into an upstream
        // crate, so we can skip them.
        if tcx.upstream_monomorphizations_for(def_id)
                .map_or(false, |monos| monos.contains_key(&inst.substs)) {
            return Ok(());
        }
    }

    // Look up and monomorphize the MIR for this instance.
    let mut mir = tcx.optimized_mir(inst_def_id(inst)).clone();
    subst_const_tys(tcx, inst.substs, &mut mir);
    let mir = tcx.subst_and_normalize_erasing_regions(
        inst.substs, ty::ParamEnv::reveal_all(), &mir);
    let mir = tcx.arena.alloc(mir);

    emit_fn(ms, out, &name, Some(inst), mir)
}


fn emit_vtable<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> io::Result<()> {
    let ti = TraitInst::from_trait_ref(ms.state.tcx, *trait_ref.skip_binder());
    out.emit(EntryKind::Vtable, json!({
        "trait_id": trait_inst_id_str(ms.state.tcx, &ti),
        "name": vtable_name(ms, trait_ref),
        "items": build_vtable_items(ms, trait_ref),
    }))?;
    emit_new_types(ms, out)
}

fn vtable_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> String {
    ext_def_id_str(mir.state.tcx, trait_ref.def_id(), "_vtbl", trait_ref)
}

fn build_vtable_items<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> serde_json::Value {
    let tcx = mir.state.tcx;
    let methods = tcx.vtable_methods(trait_ref);

    let mut parts = Vec::with_capacity(methods.len());
    for &m in methods {
        // `m` is `None` for methods with `where Self: Sized`.  We omit these from the vtable, and
        // adjust `InstanceDef::Virtual` indices accordingly.
        let (def_id, substs) = match m {
            Some(x) => x,
            None => continue,
        };
        parts.push(json!({
            "item_id": def_id.to_json(mir),
            // `def_id` is the name of the concrete function.
            "def_id": get_fn_def_name(mir, def_id, substs),
        }));
    }
    parts.into()
}


fn emit_adt<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    def_id: DefId,
) -> io::Result<()> {
    let tcx = ms.state.tcx;

    let ty = tcx.type_of(def_id);
    if let Some(adt_def) = ty.ty_adt_def() {
        let adt_name = def_id_str(tcx, def_id);
        tcx.sess.note_without_error(
            format!("Emitting ADT definition for {}", adt_name).as_str());
        out.emit(EntryKind::Adt, adt_def.tojson(ms, List::empty()))?;
        emit_new_types(ms, out)?;
    }
    Ok(())
}


/// Output a MIR body to `out.fns`.  Recursively emits all promoted statics from the body.
fn emit_fn<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    name: &str,
    inst: Option<ty::Instance<'tcx>>,
    mir: &'tcx Body<'tcx>,
) -> io::Result<()> {
    ms.state.session.note_without_error(&format!("Emitting MIR for {}", name));

    let mut ms = MirState {
        mir: Some(mir),
        used: ms.used,
        state: ms.state,
        tys: ms.tys,
    };
    let ms = &mut ms;

    let mut promoted = Vec::with_capacity(mir.promoted.len());
    for (idx, prom_mir) in mir.promoted.iter_enumerated() {
        let prom_name = format!("{}::{{{{promoted}}}}[{}]", name, idx.as_usize());
        emit_fn(ms, out, &prom_name, None, prom_mir)?;
        emit_static_decl(ms, out, &prom_name, prom_mir.return_ty(), false,
            Some((name, idx.as_usize())))?;
        promoted.push(prom_name);
    }

    let abi = inst.map(|i| inst_abi(ms.state.tcx, i)).unwrap_or(abi::Abi::Rust);

    out.emit(EntryKind::Fn, json!({
        "name": &name,
        "args": mir.args_iter().map(|l| local_json(ms, l)).collect::<Vec<_>>(),
        "return_ty": mir.return_ty().to_json(ms),
        "generics": { "params": [] },
        "predicates": { "predicates": [] },
        "body": mir_body(ms),
        "promoted": promoted,
        "abi": abi.to_json(ms),
        "spread_arg": mir.spread_arg.map(|x| x.as_usize()),
    }))?;
    emit_new_types(ms, out)
}

fn emit_new_types(
    ms: &mut MirState,
    out: &mut impl JsonOutput,
) -> io::Result<()> {
    for j in ms.tys.take_new_types() {
        out.emit(EntryKind::Ty, j)?;
    }
    assert!(ms.tys.take_new_types().is_empty());
    Ok(())
}

fn emit_entry<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    kind: EntryKind,
    j: serde_json::Value,
) -> io::Result<()> {
    out.emit(kind, j)?;
    emit_new_types(ms, out)
}

fn inst_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: ty::Instance<'tcx>,
) -> abi::Abi {
    match inst.def {
        ty::InstanceDef::Item(def_id) => {
            let ty = tcx.type_of(def_id);
            match ty.sty {
                ty::TyKind::FnDef(_, _) =>
                    ty.fn_sig(tcx).skip_binder().abi,
                ty::TyKind::Closure(_, _) => abi::Abi::RustCall,
                _ => abi::Abi::Rust,
            }
        },
        ty::InstanceDef::Intrinsic(_) => abi::Abi::RustIntrinsic,
        ty::InstanceDef::ClosureOnceShim { .. } => abi::Abi::RustCall,
        _ => abi::Abi::Rust,
    }
}


#[derive(Debug)]
pub struct AnalysisData<O> {
    pub mir_path: PathBuf,
    pub extern_mir_paths: Vec<PathBuf>,
    pub output: O,
}

/// Analyze the crate currently being compiled by `comp`.  Returns `Ok(Some(data))` upon
/// successfully writing the crate MIR, returns `Ok(None)` when there is no need to write out MIR
/// (namely, when `comp` is not producing an `Exe` output), and returns `Err(e)` on I/O or
/// serialization errors.
fn analyze_inner<O: JsonOutput, F: FnOnce(&Path) -> io::Result<O>>(
    comp: &Compiler,
    mk_output: F,
) -> Result<Option<AnalysisData<O>>, serde_cbor::Error> {
    let mut mir_path = None;
    let mut extern_mir_paths = Vec::new();
    let mut gcx = comp.global_ctxt().unwrap().peek_mut();
    let output = gcx.enter(|tcx| -> io::Result<_> {
        let outputs = tcx.output_filenames(LOCAL_CRATE);
        if !outputs.outputs.contains_key(&OutputType::Exe) {
            return Ok(None);
        }
        let mir_path_ = rustc_codegen_utils::link::out_filename(
            tcx.sess,
            tcx.sess.crate_types.get().first().unwrap().clone(),
            &outputs,
            &tcx.crate_name.to_string(),
        ).with_extension("mir");
        let mut out = mk_output(&mir_path_)?;
        mir_path = Some(mir_path_);

        for &cnum in tcx.all_crate_nums(LOCAL_CRATE) {
            let src = tcx.used_crate_source(cnum);
            let it = src.dylib.iter()
                .chain(src.rlib.iter())
                .chain(src.rmeta.iter());
            for &(ref path, _) in it {
                let mir_path = path.with_extension("mir");
                if mir_path.exists() {
                    extern_mir_paths.push(mir_path);
                    // Add only one copy of the MIR for a crate, even when we have multiple
                    // versions of the crate (such as `.so` and `.rlib`).
                    break;
                }
            }
        }


        let mut used = Used::default();
        let mut tys = TyIntern::default();
        let state = CompileState {
            session: comp.session(),
            tcx,
        };
        let mut ms = MirState {
            mir: None,
            used: &mut used,
            state: &state,
            tys: &mut tys,
        };

        // Traits and top-level statics can be enumerated directly.
        emit_statics(&mut ms, &mut out)?;

        // Everything else is demand-driven, to handle monomorphization.  We start with all #[test]
        // functions, then keep looping until there are no more nodes to process.
        init_instances(&mut ms, &mut out)?;

        while ms.used.has_new() {
            for inst in ms.used.instances.take_new() {
                emit_instance(&mut ms, &mut out, inst)?;
            }
            for vtable in ms.used.vtables.take_new() {
                emit_vtable(&mut ms, &mut out, vtable)?;
            }
            for adt in ms.used.types.take_new() {
                emit_adt(&mut ms, &mut out, adt)?;
            }
            for ti in ms.used.traits.take_new() {
                emit_trait(&mut ms, &mut out, ti)?;
            }
        }

        // Any referenced types should normally be emitted immediately after the entry that
        // references them, but we check again here just in case.
        emit_new_types(&mut ms, &mut out)?;

        Ok(Some(out))
    })?;

    let mir_path = match mir_path {
        Some(x) => x,
        None => return Ok(None),
    };
    // `output` should be `Some` if `mir_path` was `Some`.
    let output = output.unwrap();

    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output }))
}

pub fn analyze_nonstreaming(comp: &Compiler) -> Result<Option<AnalysisData<()>>, serde_cbor::Error> {
    let opt_ad = analyze_inner(comp, |_| { Ok(lib_util::Output::default()) })?;
    let AnalysisData { mir_path, extern_mir_paths, output: out } = match opt_ad {
        Some(x) => x,
        None => return Ok(None),
    };

    let total_items = out.fns.len() + out.adts.len() + out.statics.len() + out.vtables.len() +
        out.traits.len() + out.intrinsics.len();
    let j = json!({
        "fns": out.fns,
        "adts": out.adts,
        "statics": out.statics,
        "vtables": out.vtables,
        "traits": out.traits,
        "intrinsics": out.intrinsics,
        "impls": [],
        "tys": out.tys,
        "roots": out.roots,
    });
    comp.session().note_without_error(
        &format!("Indexing MIR ({} items)...", total_items));
    let file = File::create(&mir_path)?;
    lib_util::write_indexed_crate(file, &j)?;

    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: () }))
}

pub fn analyze_streaming(comp: &Compiler) -> Result<Option<AnalysisData<()>>, serde_cbor::Error> {
    let opt_ad = analyze_inner(comp, lib_util::start_streaming)?;
    let AnalysisData { mir_path, extern_mir_paths, output } = match opt_ad {
        Some(x) => x,
        None => return Ok(None),
    };
    lib_util::finish_streaming(output)?;
    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: () }))
}

pub use self::analyze_streaming as analyze;

// format:
// top: function name || function args || return ty || body
// args: name || type || scope || mutability
// body: all locals || all basicblocks
// basicblock: all statements || terminator
