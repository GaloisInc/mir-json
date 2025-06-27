#![macro_use]

use rustc_ast::{ast, token, tokenstream, ptr, Crate};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_index::Idx;
use rustc_middle::ty::{self, TyCtxt, List};
use rustc_middle::mir::{self, Body};
use rustc_middle::mir::mono::MonoItem;
use rustc_session;
use rustc_session::config::{OutputType, OutFileName};
use rustc_span::Span;
use rustc_span::symbol::{Symbol, Ident};
use rustc_abi::{self, ExternAbi};
use std::fmt::Write as FmtWrite;
use std::io;
use std::iter;
use std::fs::File;
use std::path::{Path, PathBuf};
use serde_json;
use serde_cbor;

#[macro_use]
mod to_json;
mod ty_json;
use analyz::to_json::*;
use analyz::ty_json::*;
use lib_util::{self, JsonOutput, EntryKind};
use schema_ver::SCHEMA_VER;

impl<'tcx> ToJson<'tcx> for rustc_abi::VariantIdx {
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
                    // crucible-mir uses the same representation for closures as it does for
                    // tuples, so no additional information is needed.
                })
            }
            &mir::AggregateKind::Coroutine(_, _,) => {
                // TODO
                json!({"kind": "Coroutine"})
            }
            &mir::AggregateKind::CoroutineClosure(_, _,) => {
                // TODO
                json!({"kind": "CoroutineClosure"})
            }
            &mir::AggregateKind::RawPtr(ty, mutbl) => {
                json!({
                    "kind": "RawPtr",
                    "ty": ty.to_json(mir),
                    "mutbl": mutbl.to_json(mir),
                })
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
    let tcx = mir.tcx;

    let is_unsize_cast = matches!(
        kind, mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _));
    if !is_unsize_cast {
        return None;
    }

    fn instantiate_field_ty<'tcx>(
        tcx: TyCtxt<'tcx>,
        field_def: &ty::FieldDef,
        args: ty::GenericArgsRef<'tcx>
    ) -> ty::Ty<'tcx> {
        let field_unsubst_ty = tcx.type_of(field_def.did);
        tcx.instantiate_and_normalize_erasing_regions(
            args, ty::TypingEnv::fully_monomorphized(), field_unsubst_ty
        )
    }

    match (*old_ty.kind(), *new_ty.kind()) {
        // The two base cases: we are casting between two references or two raw
        // pointers.
        (ty::TyKind::Ref(_, old_pointee, _), ty::TyKind::Ref(_, new_pointee, _)) |
        (ty::TyKind::RawPtr(old_pointee, _), ty::TyKind::RawPtr(new_pointee, _)) => {
            if !tcx.is_sized_raw(ty::TypingEnv::fully_monomorphized().as_query_input(old_pointee)) {
                // We produce a vtable only for sized -> TyDynamic casts.
                return None;
            }

            // Relevant code: rustc_codegen_ssa::meth::get_vtable
            let trait_ref = match *new_pointee.kind() {
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
        },

        // It is also possible to cast between two arbitrary struct values that
        // implement the std::ops::CoerceUnsized marker trait, provided that
        // each struct type differs in exactly one field (or a field within
        // another struct field) that supports a vtable descriptor cast. (e.g.,
        // casting from Arc<Foo> to Arc<dyn Bar>).
        (ty::TyKind::Adt(old_adt_def, old_args), ty::TyKind::Adt(new_adt_def, new_args))
          if old_adt_def.is_struct() && new_adt_def.is_struct() => {
            // Compute the fields from each struct value, and ensure that there
            // are an equal number of fields as a sanity check.
            let old_fields = &old_adt_def.non_enum_variant().fields;
            let new_fields = &new_adt_def.non_enum_variant().fields;
            if old_fields.len() != new_fields.len() {
                return None;
            }

            // Recursively walk over the fields of each struct value, and for
            // each pair of unequal fields, recursively compute their vtable
            // descriptor cast.
            let mut vtable: Option<ty::PolyTraitRef<'tcx>> = None;
            let mut unequal_fields_count: usize = 0;
            for (old_field_def, new_field_def) in old_fields.iter().zip(new_fields.iter()) {
                let old_field_ty = instantiate_field_ty(tcx, old_field_def, old_args);
                let new_field_ty = instantiate_field_ty(tcx, new_field_def, new_args);
                if old_field_ty != new_field_ty {
                    // Rust specifically allows for excess `PhantomData` fields
                    // in `CoerceUnsized` sources/targets - see
                    // https://github.com/rust-lang/rfcs/pull/1234 and
                    // https://github.com/rust-lang/rust/pull/28381 (the latter
                    // of which implemented the check we use here,
                    // `Ty::is_phantom_data`, for precisely this case). This
                    // permits definitions like `Arc`'s, which is roughly:
                    // ```
                    // struct Arc<T: ?Sized> {
                    //     ptr: NonNull<ArcInner<T>>,
                    //     phantom: PhantomData<ArcInner<T>>,
                    // }
                    // ```
                    // For details on why this is useful, see
                    // https://github.com/rust-lang/rfcs/blob/master/text/0769-sound-generic-drop.md#phantom-data.
                    if old_field_ty.is_phantom_data() && new_field_ty.is_phantom_data() {
                        continue;
                    }

                    unequal_fields_count += 1;
                    vtable = vtable_descriptor_for_cast(mir, kind, old_field_ty, new_field_ty);
                }
            }

            // If we have found exactly one pair of unequal fields (modulo
            // `PhantomData` fields, as described above), then use the resulting
            // vtable descriptor cast.
            if unequal_fields_count == 1 { vtable } else { None }
        },
        _ => None,
    }
}

/// Compute the callee method for a closure-to-fnptr cast, if applicable.
fn closure_fn_ptr_callee_for_cast<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    kind: mir::CastKind,
    old_ty: ty::Ty<'tcx>,
) -> Option<ty::Instance<'tcx>> {
    let is_closure_fn_ptr_cast = matches!(kind, mir::CastKind::PointerCoercion(
            ty::adjustment::PointerCoercion::ClosureFnPointer(_), _));
    if !is_closure_fn_ptr_cast {
        return None;
    }

    // Based on logic in `rustc_const_eval::interpret::cast,` method `InterpCx::cast`.
    let (def_id, args) = match *old_ty.kind() {
        ty::Closure(def_id, args) => (def_id, args),
        _ => return None,
    };
    let instance = ty::Instance::resolve_closure(
        mir.tcx,
        def_id,
        args,
        ty::ClosureKind::FnOnce,
    );
    Some(instance)
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
                    "len": get_const_usize(mir.tcx, s)
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
                    "def_id": did.to_json(mir),
                    "ty": mir.tcx
                        .static_ptr_ty(did, ty::TypingEnv::fully_monomorphized())
                        .to_json(mir),
                })
            }
            &mir::Rvalue::RawPtr(kind, ref l) => {
                json!({
                    "kind": "AddressOf",
                    "mutbl": kind.to_mutbl_lossy().to_json(mir),
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
                let op_ty = op.ty(mir.mir.unwrap(), mir.tcx);
                if let Some(vtable_desc) = vtable_descriptor_for_cast(mir, *ck, op_ty, ty) {
                    // On the Haskell side, the vtable is attached to the cast kind.
                    j["type"] = json!({
                        "kind": "UnsizeVtable",
                        "vtable": vtable_name(mir, vtable_desc),
                    });
                    mir.used.vtables.insert(vtable_desc);
                }
                if let Some(callee_inst) = closure_fn_ptr_callee_for_cast(mir, *ck, op_ty) {
                    let shim_inst = FnInst::ClosureFnPointer(callee_inst);
                    mir.used.instances.insert(shim_inst);
                    j["type"] = json!({
                        "kind": "ClosureFnPointer",
                        "shim": inst_id_str(mir.tcx, shim_inst),
                    });
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
                json!({
                    "kind": "Discriminant",
                    "val": lv.to_json(mir),
                    "ty": lv.ty(mir.mir.unwrap(), mir.tcx)
                            .ty
                            .discriminant_ty(mir.tcx)
                            .to_json(mir),
                })
            }
            &mir::Rvalue::Aggregate(ref ak, ref opv) => {
                if ty_json::is_adt_ak(ak) {
                    let ty = self.ty(mir.mir.unwrap(), mir.tcx);
                    json!({
                        "kind": "AdtAg",
                        "ag": ty_json::handle_adt_ag(mir, ak, opv, ty)
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
            &mir::Rvalue::WrapUnsafeBinder(ref op, ty) => {
                json!({
                    "kind": "WrapUnsafeBinder",
                    "op": op.to_json(mir),
                    "ty": ty.to_json(mir),
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
            &mir::ProjectionElem::UnwrapUnsafeBinder(ref ty) => {
                json!({"kind": "UnwrapUnsafeBinder", "ty": ty.to_json(mir) })
            }
            &mir::ProjectionElem::Subtype(ref ty) => {
                json!({"kind": "Subtype", "ty": ty.to_json(mir) })
            }
        }
    }
}

impl ToJson<'_> for rustc_abi::FieldIdx {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(self.index())
    }
}

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

impl<'tcx> ToJson<'tcx> for mir::ConstOperand<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        (eval_mir_constant(mir.tcx, self), self.ty()).to_json(mir)
    }
}

impl<'tcx> ToJson<'tcx> for mir::LocalDecl<'tcx> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "mut": self.mutability.to_json(mir),
            "ty": self.ty.to_json(mir),
            // We specifically record whether the variable's type is zero-sized, because rustc
            // allows reading and taking refs of uninitialized zero-sized locals.
            "is_zst": mir.tcx.layout_of(
                ty::TypingEnv::fully_monomorphized().as_query_input(self.ty),
            ).expect("failed to get layout").is_zst(),
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
            &mir::StatementKind::PlaceMention(ref pl) => {
                json!({
                    "kind": "PlaceMention",
                    "lvalue": pl.to_json(mir),
                })
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
            &mir::StatementKind::Intrinsic(ref ndi) => {
                match **ndi {
                    mir::NonDivergingIntrinsic::Assume(ref a) =>
                        json!({
                            "kind": "Intrinsic",
                            "intrinsic_kind": "Assume",
                            "operand": a.to_json(mir),
                        }),
                    mir::NonDivergingIntrinsic::CopyNonOverlapping(ref cno) =>
                        json!({
                            "kind": "Intrinsic",
                            "intrinsic_kind": "CopyNonOverlapping",
                            "src": cno.src.to_json(mir),
                            "dst": cno.dst.to_json(mir),
                            "count": cno.count.to_json(mir),
                        })
                }
                // TODO
                //json!({"kind": "Intrinsic" })
            }
            &mir::StatementKind::ConstEvalCounter => {
                json!({"kind": "ConstEvalCounter"})
            }
            &mir::StatementKind::BackwardIncompatibleDropHint { .. }=> {
                json!({"kind": "BackwardIncompatibleDropHint"})
            }
        };
        j["pos"] = self.source_info.span.to_json(mir);
        j
    }
}

impl ToJson<'_> for Span {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        let source_map = mir.tcx.sess.source_map();
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
                json!({
                    "kind": "SwitchInt",
                    "discr": discr.to_json(mir),
                    "values": vals,
                    "targets": targets.all_targets().iter().map(|x| x.to_json(mir))
                        .collect::<Vec<_>>(),
                    "switch_ty": discr.ty(mir.mir.unwrap(), mir.tcx).to_json(mir)
                })
            }
            &mir::TerminatorKind::UnwindResume => {
                json!({"kind": "Resume"})
            }
            &mir::TerminatorKind::UnwindTerminate(_) => {
                json!({ "kind": "Abort" })
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
                unwind: _,
                replace: _,
            } => {
                let ty = location.ty(mir.mir.unwrap(), mir.tcx).ty;
                json!({
                    "kind": "Drop",
                    "location": location.to_json(mir),
                    "target" : target.to_json(mir),
                    "drop_fn": get_drop_fn_name(mir, ty),
                })
            }
            &mir::TerminatorKind::Call {
                ref func,
                ref args,
                destination: ref dest_place,
                target: ref dest_block,
                unwind: _,
                call_source: _,
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
                })
            }
            // See https://github.com/GaloisInc/mir-json/issues/110
            &mir::TerminatorKind::TailCall {
                func: _,
                args: _,
                fn_span: _,
            } => {
                json!({"kind": "Unsupported"})
            }
            &mir::TerminatorKind::Assert {
                ref cond,
                ref expected,
                ref msg,
                ref target,
                unwind: _,
            } => {
                json!({
                    "kind": "Assert",
                    "cond": cond.to_json(mir),
                    "expected": expected,
                    "msg": msg.to_json(mir),
                    "target": target.to_json(mir),
                })
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
            &mir::TerminatorKind::CoroutineDrop => {
                json!({ "kind": "CoroutineDrop" })
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
    let tcx = ms.tcx;
    let methods = if let Some(tref) = ti.concrete_trait_ref(tcx) {
        tcx.vtable_entries(tref)
    } else {
        &[]
    };
    let mut items = Vec::with_capacity(methods.len());
    for &m in methods {
        // `m` is `None` for methods with `where Self: Sized`.  We omit these from the vtable, and
        // adjust `InstanceKind::Virtual` indices accordingly.
        let (def_id, args) = match m {
            ty::vtable::VtblEntry::Method(inst) => (inst.def.def_id(), inst.args),
            _ => continue,
        };
        let sig = tcx.instantiate_and_normalize_erasing_regions(
            args, ty::TypingEnv::fully_monomorphized(), tcx.fn_sig(def_id));
        let sig = tcx.instantiate_bound_regions_with_erased(sig);

        items.push(json!({
            "kind": "Method",
            "item_id": def_id.to_json(ms),
            "signature": sig.to_json(ms),
        }));
    }

    ms.tcx.sess.dcx().note(format!("Emitting trait def for {:?}", ti.dyn_ty(tcx)));

    out.emit(EntryKind::Trait, json!({
        // `name` corresponds to `trait_id` in vtables, Virtual, and Dynamic types.
        "name": trait_inst_id_str(ms.tcx, &ti),
        "items": items,
    }))?;
    emit_new_defs(ms, out)?;
    Ok(())
}


/// Emit all statics defined in the current crate.
fn emit_statics(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let parts = ms.tcx.collect_and_partition_mono_items(());
    for cgu in parts.codegen_units {
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
    let tcx = ms.tcx;
    let name = def_id_str(tcx, def_id);

    // let mir = tcx.optimized_mir(def_id);
    let mir = tcx.mir_for_ctfe(def_id);
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
        "kind": "body",
    });
    out.emit(EntryKind::Static, j)?;
    emit_new_defs(ms, out)
}


fn has_test_attr(tcx: TyCtxt, def_id: DefId) -> bool {
    if !def_id.is_local() {
        return false;
    }

    let crux = Symbol::intern("crux");
    let test = Symbol::intern("test");
    for attr in tcx.get_attrs_unchecked(def_id) {
        match &attr.kind {
            rustc_hir::AttrKind::Normal(ref na) => {
                let segs = &na.path.segments;
                if segs.len() == 2 && segs[0].name == crux && segs[1].name == test {
                    return true;
                }
            }
            _ => { }
        }
    }
    return false;
}

/// Process the initial/root instances in the current crate.  This adds entries to `ms.used`, and
/// may also call `out.add_root` if this is a top-level crate.
fn init_instances(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let is_top_level = ms.tcx.sess.psess.config.iter()
        .any(|&(key, _)| key.as_str() == "crux_top_level");

    if is_top_level {
        init_instances_from_tests(ms, out)
    } else {
        init_instances_from_mono_items(ms)
    }
}

/// Add every `MonoItem::Fn` to `ms.used.instances`.
fn init_instances_from_mono_items(ms: &mut MirState) -> io::Result<()> {
    let parts = ms.tcx.collect_and_partition_mono_items(());
    for cgu in parts.codegen_units {
        for mono_item in cgu.items().keys() {
            match *mono_item {
                MonoItem::Fn(inst) => ms.used.instances.insert(inst.into()),
                MonoItem::Static(_) |
                MonoItem::GlobalAsm(_) => {},
            }
        }
    }
    Ok(())
}

/// Initialize the set of needed instances.  Returns a list of root instances.
fn init_instances_from_tests(ms: &mut MirState, out: &mut impl JsonOutput) -> io::Result<()> {
    let tcx = ms.tcx;
    for &local_def_id in tcx.mir_keys(()) {
        let def_id = local_def_id.to_def_id();
        if ms.export_style == ExportStyle::ExportCruxTests && !has_test_attr(tcx, def_id) {
            continue;
        }

        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            // If the DefId does not correspond to a function, then don't mark
            // the function as a root. For crux-rustc, then also throw an error,
            // as it doesn't make sense for a user to attach a #[crux::test]
            // attribute on anything besides functions. For saw-rustc, however,
            // it is fine to move on without emitting an error, as there are
            // likely other functions elsewhere in the code that will instead
            // be marked as roots. See #55.
            if ms.export_style == ExportStyle::ExportCruxTests {
                tcx.sess.dcx().span_err(
                    tcx.def_span(def_id),
                    "#[test] can only be applied to functions",
                );
            }
            continue;
        }
        if tcx.generics_of(def_id).count() > 0 {
            // If we are using crux-rustc, then attempting to mark a generic
            // function as a root constitutes a hard error. If we are using
            // saw-rustc, however, then we simply do not mark the generic
            // function as a root and move on. This is fine to do, since there
            // is likely other monomorphic code that the user _actually_ wants
            // to verify next to the polymorphic code. See #52.
            if ms.export_style == ExportStyle::ExportCruxTests {
                tcx.sess.dcx().span_err(
                    tcx.def_span(def_id),
                    "#[test] cannot be applied to generic functions",
                );
            }
            continue;
        }

        let inst = ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), def_id, List::empty())
            .unwrap_or_else(|_| {
                panic!("Instance::resolve failed to find test function {:?}?", def_id);
            })
            .unwrap_or_else(|| {
                panic!("ambiguous Instance::resolve for find test function {:?}?", def_id);
            });

        ms.used.instances.insert(inst.into());
        out.add_root(inst_id_str(tcx, inst))?;
    }
    Ok(())
}


/// Add a single `Instance` to `out.fns` and/or `out.intrinsics`, depending on its kind.
fn emit_instance<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    inst: FnInst<'tcx>,
) -> io::Result<()> {
    let tcx = ms.tcx;

    let name = inst_id_str(tcx, inst);

    // We actually record every instance in `intrinsics`, not just `InstanceKind::Intrinsic` and
    // other special functions, because the intrinsics table is used to look up CustomOps.
    // (CustomOps are keyed on the pre-monomorphization name of the function.)
    out.emit(EntryKind::Intrinsic, json!({
        "name": &name,
        "inst": inst.to_json(ms),
    }))?;
    emit_new_defs(ms, out)?;

    let ty_inst = match inst {
        FnInst::Real(ty_inst) => {
            match ty_inst.def {
                ty::InstanceKind::Item(def_id) => {
                    // Foreign items and non-generics have no MIR available.
                    if tcx.is_foreign_item(def_id) {
                        return Ok(());
                    }
                    if !def_id.is_local() {
                        if tcx.is_reachable_non_generic(def_id) {
                            return Ok(());
                        }
                        // Items with upstream monomorphizations have already been translated into
                        // an upstream crate, so we can skip them.
                        if tcx.upstream_monomorphizations_for(def_id)
                                .map_or(false, |monos| monos.contains_key(&ty_inst.args)) {
                            return Ok(());
                        }
                    }
                },
                // These variants are unsupported by the `mir_shims` query, which backs
                // `instance_mir`.
                ty::InstanceKind::Virtual(..) |
                ty::InstanceKind::Intrinsic(..) => return Ok(()),
                _ => {},
            }
            ty_inst
        },
        // We don't generate MIR for `ClosureFnPointer` shims.  Instead, we generate code in
        // crucible-mir to implement this shim.
        FnInst::ClosureFnPointer(_) => return Ok(()),
    };

    // Look up and monomorphize the MIR for this instance.
    let mir: Body = ty_inst.instantiate_mir_and_normalize_erasing_regions(
        tcx,
        ty::TypingEnv::fully_monomorphized(),
        ty::EarlyBinder::bind(tcx.instance_mir(ty_inst.def).clone()),
    );
    let mir = tcx.arena.alloc(mir);
    emit_fn(ms, out, &name, Some(ty_inst), mir)?;

    if let ty::InstanceKind::Item(def_id) = ty_inst.def {
        for (idx, mir) in tcx.promoted_mir(def_id).iter_enumerated() {
            let mir = ty_inst.instantiate_mir_and_normalize_erasing_regions(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(mir.clone()),
            );
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
    poly_trait_ref: ty::PolyTraitRef<'tcx>,
) -> io::Result<()> {
    let trait_ref = ms.tcx.instantiate_bound_regions_with_erased(poly_trait_ref);
    let ti = TraitInst::from_trait_ref(ms.tcx, trait_ref);
    out.emit(EntryKind::Vtable, json!({
        "trait_id": trait_inst_id_str(ms.tcx, &ti),
        "name": vtable_name(ms, poly_trait_ref),
        "items": build_vtable_items(ms, poly_trait_ref),
    }))?;
    emit_new_defs(ms, out)
}

fn vtable_name<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> String {
    ext_def_id_str(mir.tcx, trait_ref.def_id(), "_vtbl", trait_ref)
}

fn build_vtable_items<'tcx>(
    mir: &mut MirState<'_, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
) -> serde_json::Value {
    let tcx = mir.tcx;
    let trait_ref = tcx.instantiate_bound_regions_with_erased(trait_ref);
    let methods = tcx.vtable_entries(trait_ref);

    let mut parts = Vec::with_capacity(methods.len());
    for &m in methods {
        // `m` is `None` for methods with `where Self: Sized`.  We omit these from the vtable, and
        // adjust `InstanceKind::Virtual` indices accordingly.
        let (def_id, args) = match m {
            ty::vtable::VtblEntry::Method(inst) => (inst.def.def_id(), inst.args),
            _ => continue,
        };
        parts.push(json!({
            "item_id": def_id.to_json(mir),
            // `def_id` is the name of the concrete function.
            "def_id": get_fn_def_name(mir, def_id, args),
        }));
    }
    parts.into()
}


fn emit_adt<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    out: &mut impl JsonOutput,
    ai: AdtInst<'tcx>,
) -> io::Result<()> {
    let tcx = ms.tcx;

    // Render the string for the ADT instance (i.e., the ADT applied to its type
    // arguments). This will go into the `adts` section of the output.
    let adt_inst_name = adt_inst_id_str(tcx, ai);
    tcx.sess.dcx().note(format!("Emitting ADT definition for {}", adt_inst_name));
    out.emit(EntryKind::Adt, ai.to_json(ms))?;

    // Render the string for the original ADT definition (i.e., the ADT *before*
    // it is applied to any type arguments). If the original ADT is a lang item,
    // then this will go into the `lang_items` section of the output.
    let adt_orig_did = ai.adt.did();
    let adt_orig_name = orig_def_id_str(tcx, adt_orig_did);
    let adt_orig_lang_item_name = lang_item_def_id_str(tcx, adt_orig_did);
    emit_lang_item(out, &adt_orig_name, adt_orig_lang_item_name.as_deref())?;

    emit_new_defs(ms, out)?;
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
    ms.tcx.sess.dcx().note(format!("Emitting MIR for {}", name));

    let mut ms = MirState {
        mir: Some(mir),
        used: ms.used,
        tcx: ms.tcx,
        tys: ms.tys,
        allocs: ms.allocs,
        export_style: ms.export_style,
    };
    let ms = &mut ms;

    let abi = inst.map(|i| inst_abi(ms.tcx, i)).unwrap_or(ExternAbi::Rust);

    out.emit(EntryKind::Fn, json!({
        "name": &name,
        "args": mir.args_iter().map(|l| local_json(ms, l)).collect::<Vec<_>>(),
        "return_ty": mir.return_ty().to_json(ms),
        "body": mir_body(ms),
        "abi": abi.to_json(ms),
        "spread_arg": mir.spread_arg.map(|x| x.as_usize()),
    }))?;
    emit_new_defs(ms, out)
}

/// If an identifier is a lang item (i.e., if the supplied
/// `lang_item_def_id_str` is a `Some` value), then output the lang item's ID
/// and its original ID to `out.lang_items`. Otherwise, do nothing.
fn emit_lang_item(
    out: &mut impl JsonOutput,
    orig_def_id_str: &str,
    lang_item_def_id_str: Option<&str>,
) -> io::Result<()> {
    match lang_item_def_id_str {
        None => {
            io::Result::Ok(())
        },
        Some(lang_item_def_id_str) => {
            out.emit(EntryKind::LangItem, json!({
                "name": lang_item_def_id_str,
                "orig_def_id": orig_def_id_str,
            }))
        },
    }
}

fn emit_new_defs(
    ms: &mut MirState,
    out: &mut impl JsonOutput,
) -> io::Result<()> {
    for j in ms.tys.take_new_types() {
        out.emit(EntryKind::Ty, j)?;
    }
    for j in ms.allocs.take_new_allocs() {
        out.emit(EntryKind::Static, j)?;
    }
    assert!(ms.tys.take_new_types().is_empty());
    Ok(())
}

fn inst_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    inst: ty::Instance<'tcx>,
) -> ExternAbi {
    match inst.def {
        ty::InstanceKind::Item(def_id) => {
            // OK to ignore binders, since we're only looking at the function's ABI.
            let ty = tcx.type_of(def_id).skip_binder();
            match *ty.kind() {
                ty::TyKind::FnDef(_, _) =>
                    ty.fn_sig(tcx).skip_binder().abi,
                ty::TyKind::Closure(_, _) => ExternAbi::RustCall,
                _ => ExternAbi::Rust,
            }
        },
        ty::InstanceKind::Intrinsic(_) => ExternAbi::RustIntrinsic,
        ty::InstanceKind::ClosureOnceShim { .. } => ExternAbi::RustCall,
        _ => ExternAbi::Rust,
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
    tcx: TyCtxt<'tcx>,
    export_style: ExportStyle,
    mk_output: F,
) -> Result<Option<AnalysisData<O>>, serde_cbor::Error> {
    let mut extern_mir_paths = Vec::new();

    let outputs = tcx.output_filenames(());
    if !outputs.outputs.contains_key(&OutputType::Exe) {
        return Ok(None);
    }
    let out_path = rustc_session::output::out_filename(
        tcx.sess,
        tcx.crate_types().first().unwrap().clone(),
        &outputs,
        tcx.crate_name(LOCAL_CRATE),
    );
    let mir_path = match out_path {
        OutFileName::Real(path) => path.with_extension("mir"),
        OutFileName::Stdout => {
            tcx.sess.dcx().fatal("writing output to stdout is not supported");
        },
    };
    let mut out = mk_output(&mir_path)?;

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
    let mut allocs = AllocIntern::default();
    let mut ms = MirState {
        mir: None,
        used: &mut used,
        tcx,
        tys: &mut tys,
        allocs: &mut allocs,
        export_style: export_style,
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
    emit_new_defs(&mut ms, &mut out)?;

    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: out }))
}

pub fn analyze_nonstreaming<'tcx>(
    tcx: TyCtxt<'tcx>,
    export_style: ExportStyle,
) -> Result<Option<AnalysisData<()>>, serde_cbor::Error> {
    let opt_ad = analyze_inner(tcx, export_style, |_| { Ok(lib_util::Output::default()) })?;
    let AnalysisData { mir_path, extern_mir_paths, output: out } = match opt_ad {
        Some(x) => x,
        None => return Ok(None),
    };

    let total_items = out.fns.len() + out.adts.len() + out.statics.len() + out.vtables.len() +
        out.traits.len() + out.intrinsics.len();
    let j = json!({
        "version": SCHEMA_VER,
        "fns": out.fns,
        "adts": out.adts,
        "statics": out.statics,
        "vtables": out.vtables,
        "traits": out.traits,
        "intrinsics": out.intrinsics,
        "tys": out.tys,
        "lang_items": out.lang_items,
        "roots": out.roots,
    });
    tcx.sess.dcx().note(
        format!("Indexing MIR ({} items)...", total_items));
    let file = File::create(&mir_path)?;
    lib_util::write_indexed_crate(file, &j)?;

    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: () }))
}

pub fn analyze_streaming<'tcx>(
    tcx: TyCtxt<'tcx>,
    export_style: ExportStyle,
) -> Result<Option<AnalysisData<()>>, serde_cbor::Error> {
    let opt_ad = analyze_inner(tcx, export_style, lib_util::start_streaming)?;
    let AnalysisData { mir_path, extern_mir_paths, output } = match opt_ad {
        Some(x) => x,
        None => return Ok(None),
    };
    lib_util::finish_streaming(output)?;
    Ok(Some(AnalysisData { mir_path, extern_mir_paths, output: () }))
}

pub use self::analyze_streaming as analyze;
pub use analyz::to_json::ExportStyle;

fn make_attr(key: &str, value: &str) -> ast::Attribute {
    ast::Attribute {
        kind: ast::AttrKind::Normal(
            ptr::P(ast::NormalAttr {
                item: ast::AttrItem {
                    unsafety: ast::Safety::Default,
                    path: ast::Path::from_ident(Ident::from_str(key)),
                    args: ast::AttrArgs::Delimited(
                        ast::DelimArgs {
                            dspan: tokenstream::DelimSpan::dummy(),
                            delim: token::Delimiter::Parenthesis,
                            tokens: iter::once(
                                tokenstream::TokenTree::token_alone(
                                    token::TokenKind::Ident(
                                        Symbol::intern(value),
                                        token::IdentIsRaw::No,
                                    ),
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

pub fn inject_attrs<'tcx>(krate: &mut Crate) {
    krate.attrs.push(make_attr("feature", "register_tool"));
    krate.attrs.push(make_attr("register_tool", "crux"));
}
