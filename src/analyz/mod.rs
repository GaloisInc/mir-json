#![macro_use]

use rustc_ast::{ast, token, tokenstream, visit, ptr, Crate};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{self, DefId, LOCAL_CRATE};
use rustc_index::vec::Idx;
use rustc_interface::Queries;
use rustc_middle::ty::{self, TyCtxt, List};
use rustc_middle::mir::{self, Body};
use rustc_middle::mir::mono::MonoItem;
use rustc_session::{self, Session};
use rustc_session::config::OutputType;
use rustc_span::Span;
use rustc_span::symbol::{Symbol, Ident};
use rustc_target::abi;
use rustc_target::spec;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::io;
use std::iter;
use std::fs::File;
use std::mem;
use std::path::{Path, PathBuf};
use std::rc::Rc;
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

impl<'tcx> ToJson<'tcx> for abi::VariantIdx {
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
            &mir::AggregateKind::Closure(_, _) => {
                json!({
                    "kind": "Closure",
                    // mir-verifier uses the same representation for closures as it does for
                    // tuples, so no additional information is needed.
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
    let old_pointee = match *old_ty.kind() {
        ty::TyKind::Ref(_, ty, _) => ty,
        ty::TyKind::RawPtr(ref tm) => tm.ty,
        _ => return None,
    };
    let new_pointee = match *new_ty.kind() {
        ty::TyKind::Ref(_, ty, _) => ty,
        ty::TyKind::RawPtr(ref tm) => tm.ty,
        _ => return None,
    };

    if !tcx.is_sized_raw(ty::ParamEnv::reveal_all().and(old_pointee)) {
        // We produce a vtable only for sized -> TyDynamic casts.
        return None;
    }

    // Relevant code: rustc_codegen_ssa::meth::get_vtable
    let trait_ref = match *new_pointee.kind() {
        // NB nightly-2023-01-23 dyntype
        ty::TyKind::Dynamic(ref preds, _, _) =>
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
                    "len": s.to_json(mir),
                })
            }
            &mir::Rvalue::Ref(_, ref bk, ref l) => {
                json!({
                    "kind": "Ref",
                    "region": "unimplement",
                    "borrowkind": bk.to_json(mir),
                    "refvar": l.to_json(mir)
                })
            }
            &mir::Rvalue::ThreadLocalRef(did) => {
                json!({
                    "kind": "ThreadLocalRef",
                    "def_id": did.to_json(mir)
                })
            }
            &mir::Rvalue::AddressOf(mutbl, ref l) => {
                json!({
                    "kind": "AddressOf",
                    "mutbl": mutbl.to_json(mir),
                    "place": l.to_json(mir)
                })
            }
            &mir::Rvalue::Len(ref l) => {
                json!({"kind": "Len", "lv": l.to_json(mir)})
            }
            &mir::Rvalue::Cast(ref ck, ref op, ty) => {
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
            &mir::Rvalue::BinaryOp(ref binop, ref ops) => {
                json!({
                    "kind": "BinaryOp",
                    "op": binop.to_json(mir),
                    "L": ops.0.to_json(mir),
                    "R": ops.1.to_json(mir)
                })
            }
            &mir::Rvalue::CheckedBinaryOp(ref binop, ref ops) => {
                json!({
                    "kind": "CheckedBinaryOp",
                    "op": binop.to_json(mir),
                    "L": ops.0.to_json(mir),
                    "R": ops.1.to_json(mir)
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
            &mir::Rvalue::ShallowInitBox(ref op, ty) => {
                json!({
                    "kind": "ShallowInitBox",
                    "ptr": op.to_json(mir),
                    "ty": ty.to_json(mir)
                })
            }
            &mir::Rvalue::CopyForDeref(ref l) => {
                json!({
                    "kind": "CopyForDeref",
                    "place": l.to_json(mir)
                })
            }
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::Place<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "var": local_json(mir, self.local),
            "data" : self.projection.to_json(mir)
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
            &mir::ProjectionElem::Subslice { ref from, ref to, from_end } => {
                json!({
                    "kind": "Subslice",
                    "from": from,
                    "to": to,
                    "from_end": from_end,
                })
            }
            &mir::ProjectionElem::Downcast(ref _adt, ref variant) => {
                json!({"kind": "Downcast", "variant": variant.to_json(mir)})
            }
            &mir::ProjectionElem::OpaqueCast(ref ty) => {
                json!({"kind": "OpaqueCast", "variant": ty.to_json(mir) })
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
        match self.literal {
            mir::ConstantKind::Ty(c) => c.to_json(mir),
            mir::ConstantKind::Val(cv, ty) => (cv, ty).to_json(mir),
            // nightly-20203-01-22 evaluate?
            mir::ConstantKind::Unevaluated(val, ty) =>
                panic!("unevaluated const in mir::constant serializer")
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::LocalDecl<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "mut": self.mutability.to_json(mir),
            "ty": self.ty.to_json(mir),
            // We specifically record whether the variable's type is zero-sized, because rustc
            // allows reading and taking refs of uninitialized zero-sized locals.
            "is_zst": mir.state.tcx.layout_of(ty::ParamEnv::reveal_all().and(self.ty))
                .expect("failed to get layout").is_zst(),
        })
    }
}

impl<'tcx> ToJson<'tcx> for mir::Statement<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut j = match &self.kind {
            &mir::StatementKind::Assign(ref assign) => {
                json!({
                    "kind": "Assign",
                    "lhs": assign.0.to_json(mir),
                    "rhs": assign.1.to_json(mir)
                })
            }
            &mir::StatementKind::FakeRead { .. } => {
                // TODO
                json!({"kind": "FakeRead"})
            }
            &mir::StatementKind::Deinit { .. } => {
                // TODO
                json!({"kind": "Deinit"})
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
            &mir::StatementKind::Retag { .. } => {
                // TODO
                json!({"kind": "Retag"})
            }
            &mir::StatementKind::AscribeUserType { .. } => {
                // TODO
                json!({"kind": "AscribeUserType"})
            }
            &mir::StatementKind::Coverage { .. } => {
                // TODO
                json!({"kind": "Coverage"})
            }
            &mir::StatementKind::Nop => {
                json!({"kind": "Nop"})
            }
            &mir::StatementKind::Intrinsic { .. } => {
                // TODO
                json!({"kind": "Intrinsic" })
            }
        };
        j["pos"] = self.source_info.span.to_json(mir);
        j
    }
}

fn operand_span(mir: &MirState, op: &mir::Operand) -> Option<Span> {
    let local = op.place()?.as_local()?;
    Some(mir.mir?.local_decls[local].source_info.span)
}

impl ToJson<'_> for Span {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        let source_map = mir.state.session.source_map();
        let callsite = self.source_callsite();
        let s = if callsite == *self {
            // Use `span_to_diagnostic_string` to get a string with full file paths.
            source_map.span_to_diagnostic_string(*self)
        } else {
            format!(
                "{} !{}",
                source_map.span_to_diagnostic_string(*self),
                source_map.span_to_diagnostic_string(callsite),
            )
        };
        s.into()
    }
}

impl<'tcx> ToJson<'tcx> for mir::Terminator<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        let mut j = match &self.kind {
            &mir::TerminatorKind::Goto { ref target } => {
                json!({"kind": "Goto", "target": target.to_json(mir)})
            }
            &mir::TerminatorKind::SwitchInt {
                ref discr,
                ref targets,
            } => {
                let vals: Vec<String> =
                    targets.iter().map(|(c, _)| c.to_string()).collect();
                let discr_span = mir.match_span_map.get(&self.source_info.span).cloned()
                    .or_else(|| operand_span(mir, discr))
                    .unwrap_or(self.source_info.span);
                json!({
                    "kind": "SwitchInt",
                    "discr": discr.to_json(mir),
                    "discr_span": discr_span.to_json(mir),
                    "values": vals,
                    "targets": targets.all_targets().iter().map(|x| x.to_json(mir))
                        .collect::<Vec<_>>(),
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
                place: ref location,
                ref target,
                ref unwind,
            } => {
                let ty = location.ty(mir.mir.unwrap(), mir.state.tcx).ty;
                json!({
                    "kind": "Drop",
                    "location": location.to_json(mir),
                    "target" : target.to_json(mir),
                    "unwind": unwind.to_json(mir),
                    "drop_fn": get_drop_fn_name(mir, ty),
                })
            }
            &mir::TerminatorKind::DropAndReplace {
                place: ref location,
                ref value,
                ref target,
                ref unwind,
            } => {
                let ty = location.ty(mir.mir.unwrap(), mir.state.tcx).ty;
                json!({
                    "kind": "DropAndReplace",
                    "location": location.to_json(mir),
                    "value": value.to_json(mir),
                    "target": target.to_json(mir),
                    "unwind": unwind.to_json(mir),
                    "drop_fn": get_drop_fn_name(mir, ty),
                })
            }
            &mir::TerminatorKind::Call {
                ref func,
                ref args,
                destination: ref dest_place,
                target: ref dest_block,
                ref cleanup,
                ref from_hir_call,
                fn_span: _,
            } => {
                let destination = dest_block.as_ref().map(|dest_block| {
                    json!([
                        dest_place.to_json(mir),
                        dest_block.to_json(mir),
                    ])
                });
                json!({
                    "kind": "Call",
                    "func": func.to_json(mir),
                    "args": args.to_json(mir),
                    "destination": destination,
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
            &mir::TerminatorKind::FalseEdge { .. } => {
                // TODO
                json!({
                    "kind": "FalseEdge"
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
            &mir::TerminatorKind::InlineAsm { .. } => {
                // TODO
                json!({"kind": "InlineAsm"})
            }
        };
        j["pos"] = self.source_info.span.to_json(mir);
        j
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
            "terminator": self.terminator().to_json(mir)
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
    for bb in mir.basic_blocks.indices() {
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


fn emit_trait<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    ti: TraitInst<'tcx>,
) -> io::Result<()> {
    let tcx = ms.state.tcx;
    let methods = if let Some(tref) = ti.concrete_trait_ref(tcx) {
        tcx.vtable_entries(ty::Binder::dummy(tref))
    } else {
        &[]
    };
    let mut items = Vec::with_capacity(methods.len());
    for &m in methods {
        // `m` is `None` for methods with `where Self: Sized`.  We omit these from the vtable, and
        // adjust `InstanceDef::Virtual` indices accordingly.
        let (def_id, substs) = match m {
            ty::vtable::VtblEntry::Method(inst) => (inst.def.def_id(), inst.substs),
            _ => continue,
        };
        let sig = tcx.subst_and_normalize_erasing_regions(
            substs, ty::ParamEnv::reveal_all(), tcx.fn_sig(def_id));
        let sig = tcx.erase_late_bound_regions(sig);

        items.push(json!({
            "kind": "Method",
            "item_id": def_id.to_json(ms),
            "signature": sig.to_json(ms),
        }));
    }

    ms.state.session.note_without_error(&format!("Emitting trait def for {:?}", ti.dyn_ty(tcx)));

    out.emit(EntryKind::Trait, json!({
        // `name` corresponds to `trait_id` in vtables, Virtual, and Dynamic types.
        "name": trait_inst_id_str(ms.state.tcx, &ti),
        "items": items,
    }))?;
    emit_new_types(ms, out)?;
    Ok(())
}


/// Emit all statics defined in the current crate.
fn emit_statics(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let (_, cgus) = ms.state.tcx.collect_and_partition_mono_items(());
    for cgu in cgus {
        for mono_item in cgu.items().keys() {
            match *mono_item {
                MonoItem::Static(def_id) => emit_static(ms, out, def_id)?,
                MonoItem::Fn(_) |
                MonoItem::GlobalAsm(_) => {},
            }
        }
    }
    Ok(())
}

fn emit_static(ms: &mut MirState, out: &mut impl JsonOutput, def_id: DefId) -> io::Result<()> {
    let tcx = ms.state.tcx;
    let name = def_id_str(tcx, def_id);

    let mir = tcx.optimized_mir(def_id);
    emit_fn(ms, out, &name, None, mir)?;
    emit_static_decl(ms, out, &name, mir.return_ty(), tcx.is_mutable_static(def_id))?;

    for (idx, mir) in tcx.promoted_mir(def_id).iter_enumerated() {
        emit_promoted(ms, out, &name, idx, mir)?;
    }

    Ok(())
}

/// Add a new static declaration to `out.statics`.
fn emit_static_decl<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    name: &str,
    ty: ty::Ty<'tcx>,
    mutable: bool,
) -> io::Result<()> {
    let j = json!({
        "name": name,
        "ty": ty.to_json(ms),
        "mutable": mutable,
    });
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
    let (_, cgus) = ms.state.tcx.collect_and_partition_mono_items(());
    for cgu in cgus {
        for mono_item in cgu.items().keys() {
            match *mono_item {
                MonoItem::Fn(inst) => ms.used.instances.insert(inst),
                MonoItem::Static(_) |
                MonoItem::GlobalAsm(_) => {},
            }
        }
    }
    Ok(())
}

/// Initialize the set of needed instances.  Returns a list of root instances.
fn init_instances_from_tests(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let tcx = ms.state.tcx;
    for &local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();
        if !has_test_attr(tcx, def_id) {
            continue;
        }

        if tcx.def_kind(def_id) != DefKind::Fn {
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
            .unwrap_or_else(|_| {
                panic!("Instance::resolve failed to find test function {:?}?", def_id);
            })
            .unwrap_or_else(|| {
                panic!("ambiguous Instance::resolve for find test function {:?}?", def_id);
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

    match inst.def {
        ty::InstanceDef::Item(def_id) => {
            // Foreign items and non-generics have no MIR available.
            let def_id = def_id.did;
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
        },
        // These variants are unsupported by the `mir_shims` query, which backs `instance_mir`.
        ty::InstanceDef::Virtual(..) |
        ty::InstanceDef::Intrinsic(..) => return Ok(()),
        _ => {},
    }

    // Look up and monomorphize the MIR for this instance.
    let mir = tcx.instance_mir(inst.def);
    let mir: Body = tcx.subst_and_normalize_erasing_regions(
        inst.substs, ty::ParamEnv::reveal_all(), mir.clone());
    let mir = tcx.arena.alloc(mir);
    emit_fn(ms, out, &name, Some(inst), mir)?;

    if let ty::InstanceDef::Item(def_id) = inst.def {
        let def_id = def_id.did;
        for (idx, mir) in tcx.promoted_mir(def_id).iter_enumerated() {
            let mir = tcx.subst_and_normalize_erasing_regions(
                inst.substs, ty::ParamEnv::reveal_all(), mir.clone());
            let mir = tcx.arena.alloc(mir);
            emit_promoted(ms, out, &name, idx, mir)?;
        }
    }

    Ok(())
}

fn emit_promoted<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    parent: &str,
    idx: mir::Promoted,
    mir: &'tcx Body<'tcx>,
) -> io::Result<()> {
    let name = format!("{}::{{{{promoted}}}}[{}]", parent, idx.as_usize());
    emit_fn(ms, out, &name, None, mir)?;
    emit_static_decl(ms, out, &name, mir.return_ty(), false)?;
    Ok(())
}


fn emit_vtable<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> io::Result<()> {
    let ti = TraitInst::from_trait_ref(ms.state.tcx, trait_ref.skip_binder());
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
    let methods = tcx.vtable_entries(trait_ref);

    let mut parts = Vec::with_capacity(methods.len());
    for &m in methods {
        // `m` is `None` for methods with `where Self: Sized`.  We omit these from the vtable, and
        // adjust `InstanceDef::Virtual` indices accordingly.
        let (def_id, substs) = match m {
            ty::vtable::VtblEntry::Method(inst) => (inst.def.def_id(), inst.substs),
            _ => continue,
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
    ai: AdtInst<'tcx>,
) -> io::Result<()> {
    let tcx = ms.state.tcx;

    let adt_name = adt_inst_id_str(tcx, ai);
    tcx.sess.note_without_error(
        format!("Emitting ADT definition for {}", adt_name).as_str());
    out.emit(EntryKind::Adt, ai.to_json(ms))?;
    emit_new_types(ms, out)?;
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
        match_span_map: ms.match_span_map,
    };
    let ms = &mut ms;

    let abi = inst.map(|i| inst_abi(ms.state.tcx, i)).unwrap_or(spec::abi::Abi::Rust);

    out.emit(EntryKind::Fn, json!({
        "name": &name,
        "args": mir.args_iter().map(|l| local_json(ms, l)).collect::<Vec<_>>(),
        "return_ty": mir.return_ty().to_json(ms),
        "body": mir_body(ms),
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

fn inst_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: ty::Instance<'tcx>,
) -> spec::abi::Abi {
    match inst.def {
        ty::InstanceDef::Item(def_id) => {
            let def_id = def_id.did;
            let ty = tcx.type_of(def_id);
            match *ty.kind() {
                ty::TyKind::FnDef(_, _) =>
                    ty.fn_sig(tcx).skip_binder().abi,
                ty::TyKind::Closure(_, _) => spec::abi::Abi::RustCall,
                _ => spec::abi::Abi::Rust,
            }
        },
        ty::InstanceDef::Intrinsic(_) => spec::abi::Abi::RustIntrinsic,
        ty::InstanceDef::ClosureOnceShim { .. } => spec::abi::Abi::RustCall,
        _ => spec::abi::Abi::Rust,
    }
}


#[derive(Debug)]
pub struct AnalysisData<O> {
    pub mir_path: PathBuf,
    pub extern_mir_paths: Vec<PathBuf>,
    pub output: O,
}

/// Analyze the crate currently being compiled.  Returns `Ok(Some(data))` upon successfully writing
/// the crate MIR, returns `Ok(None)` when there is no need to write out MIR (namely, when `comp`
/// is not producing an `Exe` output), and returns `Err(e)` on I/O or serialization errors.
fn analyze_inner<'tcx, O: JsonOutput, F: FnOnce(&Path) -> io::Result<O>>(
    sess: &Session,
    queries: &'tcx Queries<'tcx>,
    mk_output: F,
) -> Result<Option<AnalysisData<O>>, serde_cbor::Error> {
    let mut mir_path = None;
    let mut extern_mir_paths = Vec::new();

    let output = queries.global_ctxt().unwrap().enter(|tcx| -> io::Result<_> {
        let outputs = tcx.output_filenames(());
        if !outputs.outputs.contains_key(&OutputType::Exe) {
            return Ok(None);
        }
        let mir_path_ = rustc_session::output::out_filename(
            sess,
            sess.crate_types().first().unwrap().clone(),
            &outputs,
            // nightly-2023-01-22 call symbol constructor
            tcx.crate_name(LOCAL_CRATE),
        ).with_extension("mir");
        let mut out = mk_output(&mir_path_)?;
        mir_path = Some(mir_path_);

        for &cnum in tcx.crates(()) {
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
            session: sess,
            tcx,
        };
        let mut ms = MirState {
            mir: None,
            used: &mut used,
            state: &state,
            tys: &mut tys,
            match_span_map: &get_match_spans(),
        };

        // Traits and top-level statics can be enumerated directly.
        emit_statics(&mut ms, &mut out)?;

        // Everything else is demand-driven, to handle monomorphization.  We start with all
        // #[test] functions, then keep looping until there are no more nodes to process.
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

pub fn analyze_nonstreaming<'tcx>(
    sess: &Session,
    queries: &'tcx Queries<'tcx>,
) -> Result<Option<AnalysisData<()>>, serde_cbor::Error> {
    let opt_ad = analyze_inner(sess, queries, |_| { Ok(lib_util::Output::default()) })?;
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
        "tys": out.tys,
        "roots": out.roots,
    });
    sess.note_without_error(
        &format!("Indexing MIR ({} items)...", total_items));
    let file = File::create(&mir_path)?;
    lib_util::write_indexed_crate(file, &j)?;

    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: () }))
}

pub fn analyze_streaming<'tcx>(
    sess: &Session,
    queries: &'tcx Queries<'tcx>,
) -> Result<Option<AnalysisData<()>>, serde_cbor::Error> {
    let opt_ad = analyze_inner(sess, queries, lib_util::start_streaming)?;
    let AnalysisData { mir_path, extern_mir_paths, output } = match opt_ad {
        Some(x) => x,
        None => return Ok(None),
    };
    lib_util::finish_streaming(output)?;
    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: () }))
}

pub use self::analyze_streaming as analyze;

fn make_attr(key: &str, value: &str) -> ast::Attribute {
    ast::Attribute {
        kind: ast::AttrKind::Normal(
            ptr::P(ast::NormalAttr {
                item: ast::AttrItem {
                    path: ast::Path::from_ident(Ident::from_str(key)),
                    args: ast::AttrArgs::Delimited(
                        ast::DelimArgs {
                            dspan: tokenstream::DelimSpan::dummy(),
                            delim: ast::MacDelimiter::Parenthesis,
                            tokens: iter::once(
                                tokenstream::TokenTree::token_alone(
                                    token::TokenKind::Ident(Symbol::intern(value), false),
                                    Span::default(),
                                ),
                            ).collect(),
                        }),
                    tokens: None,
                },
                tokens: None,
            })),
        id: ast::AttrId::new(0),
        style: ast::AttrStyle::Inner,
        span: Span::default(),
    }
}

pub fn inject_attrs<'tcx>(queries: &'tcx Queries<'tcx>) {
    let mut k = queries.parse().unwrap(); // need to call `get_mut`?
    let krate: &mut Crate = k.get_mut();
    krate.attrs.push(make_attr("feature", "register_attr"));
    krate.attrs.push(make_attr("register_attr", "crux_test"));
}

#[derive(Default)]
struct GatherMatchSpans {
    match_span_map: HashMap<Span, Span>,
    cur_match_discr_span: Option<Span>,
}

impl GatherMatchSpans {
    fn with_cur_match_discr_span(&mut self, val: Option<Span>, f: impl FnOnce(&mut Self)) {
        let old = mem::replace(&mut self.cur_match_discr_span, val);
        f(self);
        self.cur_match_discr_span = old;
    }
}

impl<'a> visit::Visitor<'a> for GatherMatchSpans {
    fn visit_expr(&mut self, e: &ast::Expr) {
        match e.kind {
            ast::ExprKind::Match(ref discr, ref arms) => {
                self.visit_expr(discr);

                self.with_cur_match_discr_span(Some(discr.span), |self_| {
                    for arm in arms {
                        self_.visit_arm(arm);
                    }
                });
            },
            _ => visit::walk_expr(self, e),
        }
    }

    fn visit_arm(&mut self, a: &ast::Arm) {
        // The discr span should be available in the patterns of the arm, but not its guard or body
        // expressions.
        self.visit_pat(&a.pat);
        self.with_cur_match_discr_span(None, |self_| {
            if let Some(ref e) = a.guard {
                self_.visit_expr(e);
            }
            self_.visit_expr(&a.body);
        });
    }

    fn visit_pat(&mut self, p: &ast::Pat) {
        if let Some(span) = self.cur_match_discr_span {
            self.match_span_map.insert(p.span, span);
        }
        visit::walk_pat(self, p)
    }
}

thread_local! {
    /// See documentation on `MirState::match_span_map` for info.
    ///
    /// The handling of the `match_span_map` is a little tricky.  The map must be constructed
    /// during `rustc_driver::Callbacks::after_expansion`, then used during `after_analysis`.  We'd
    /// like to pass the map from one callback to the other through our struct that implements
    /// `Callbacks`, but this is forbidden: the callbacks must implement `Send`, while `Span` is
    /// `!Send` and `!Sync`.  Instead, we pass it through this thread-local variable, and just hope
    /// that `after_expansion` and `after_analysis` get called on the same thread.  It seems likely
    /// that they will be, since both get access to data structures that contain spans, and the
    /// span interning table is also thread-local (likely this is why spans are `!Sync`).
    static MATCH_SPAN_MAP: RefCell<Option<Rc<HashMap<Span, Span>>>> = RefCell::default()
}

pub fn gather_match_spans<'tcx>(queries: &'tcx Queries<'tcx>) {
    let k = queries.expansion().unwrap();
    let krate = &k.borrow().0;
    let mut v = GatherMatchSpans::default();
    visit::walk_crate(&mut v, krate);
    MATCH_SPAN_MAP.with(|m| m.replace(Some(Rc::new(v.match_span_map))));
}

fn get_match_spans() -> Rc<HashMap<Span, Span>> {
    MATCH_SPAN_MAP.with(|m| {
        match *m.borrow() {
            Some(ref rc) => rc.clone(),
            None => panic!("MATCH_SPAN_MAP is uninitialized on this thread"),
        }
    })
}
