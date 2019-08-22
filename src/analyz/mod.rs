#![macro_use]

use rustc::ty::{self, TyCtxt, List, TyS};
use rustc::mir::{self, Body};
use rustc::hir;
use rustc::hir::def_id;
use rustc::hir::def_id::DefId;
use rustc::mir::mono::MonoItem;
use rustc::traits;
use rustc::ty::subst::Subst;
use rustc_driver::source_name;
use rustc_interface::interface::Compiler;
use rustc_mir::monomorphize::collector::{self, MonoItemCollectionMode};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;
use std::io;
use std::io::Write;
use std::fs::File;
use std::path::Path;
use serde::ser::{Serialize, Serializer, SerializeSeq};
use serde_json;

#[macro_use]
mod to_json;
mod ty_json;
use analyz::to_json::*;
use analyz::ty_json::*;

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
        if let Some((def_id, substs)) = m {
            let inst =
                ty::Instance::resolve(tcx, ty::ParamEnv::reveal_all(), def_id, substs)
                .unwrap_or_else(|| panic!("failed to resolve {:?} {:?} for vtable",
                                          def_id, substs));
            let inst_def_id = match inst.def {
                ty::InstanceDef::Item(def_id) => def_id,
                _ => panic!("instance {:?} ({:?}, {:?}) resolved to non-Item",
                            inst, def_id, substs),
            };
            parts.push(json!({
                "def_id": inst_id_str(mir.state.tcx, inst_def_id, inst.substs),
                "instance": inst.to_json(mir),
            }));
        } else {
            parts.push(json!(null));
        }
    }
    parts.into()
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

pub fn get_def_ids(tcx: TyCtxt) -> Vec<DefId> {
    tcx.mir_keys(def_id::LOCAL_CRATE)
        .iter()
        .cloned()
        .collect::<Vec<_>>()
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


pub fn local_json(ms: &mut MirState, local: mir::Local) -> serde_json::Value {
    let mut j = ms.mir.unwrap().local_decls[local].to_json(ms); // TODO
    let mut s = String::new();
    write!(&mut s, "{:?}", local).unwrap();
    j["name"] = json!(s);
    j
}

fn mir_body(
    ms: &mut MirState,
) -> serde_json::Value {
    let mir = ms.mir.unwrap(); // TODO
    let mut vars = Vec::new();

    vars.push(local_json(ms, mir::RETURN_PLACE));

    for (_, v) in ms.mir.unwrap().vars_and_temps_iter().enumerate() {
        vars.push(local_json(ms, v));
    }

    let mut blocks = Vec::new();
    for bb in mir.basic_blocks().indices() {
        //blocks.push(json!({"name": bb.to_json(), "data":mir[bb].to_json()}));
        // if it turns out theyre not in order
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

fn build_mir<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    fns: &mut Vec<serde_json::Value>,
    statics: &mut Vec<serde_json::Value>,
    name: &str,
    inst: Option<ty::Instance<'tcx>>,
    mir: &'tcx Body<'tcx>,
) -> serde_json::Value {
    let mut promoted = Vec::with_capacity(mir.promoted.len());
    for (idx, prom_mir) in mir.promoted.iter_enumerated() {
        let prom_name = format!("{}::{{{{promoted}}}}[{}]", name, idx.as_usize());

        let mut prom_ms = MirState {
            mir: Some(prom_mir),
            used: ms.used,
            state: ms.state,
        };

        let f = build_mir(&mut prom_ms, fns, statics, &prom_name, None, prom_mir);
        let s = build_static_inner(&mut prom_ms, &prom_name, prom_mir.return_ty(), false,
                                   Some((name, idx.as_usize())));
        fns.push(f);
        statics.push(s);
        promoted.push(prom_name);
    }

    json!({
        "name": &name,
        "inst": inst.to_json(ms),
        "args": mir.args_iter().map(|l| local_json(ms, l)).collect::<Vec<_>>(),
        "return_ty": mir.return_ty().to_json(ms),
        "generics": { "params": [] },
        "predicates": { "predicates": [] },
        "body": mir_body(ms),
        "promoted": promoted,
    })
}

fn build_static<'tcx>(
    state: &mut CompileState<'_, 'tcx>,
    used: &mut Used<'tcx>,
    def_id: DefId,
) -> serde_json::Value {
    let tcx = state.tcx;

    let name = def_id_str(tcx, def_id);
    let ty = tcx.type_of(def_id);
    let mutable = tcx.is_mutable_static(def_id);

    let mut ms = MirState {
        mir: None,
        used: used,
        state: state,
    };
    build_static_inner(&mut ms, &name, ty, mutable, None)
}

fn build_static_inner<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    name: &str,
    ty: ty::Ty<'tcx>,
    mutable: bool,
    promoted_info: Option<(&str, usize)>,
) -> serde_json::Value {
    let mut j = json!({
        "name": name,
        "ty": ty.to_json(ms),
        "mutable": mutable,
    });
    if let Some((parent, idx)) = promoted_info {
        j.as_object_mut().unwrap().insert("promoted_from".to_owned(), parent.into());
        j.as_object_mut().unwrap().insert("promoted_index".to_owned(), idx.into());
    }
    j
}

/// Convert all functions to JSON values.  The second output is a list of JSON values describing
/// `static` items found among the MIR functions.
pub fn emit_mono_items<'tcx>(
    state: &mut CompileState<'_, 'tcx>,
    used: &mut Used<'tcx>,
) -> (Vec<serde_json::Value>, Vec<serde_json::Value>) {
    let mut fns = Vec::new();
    let mut statics = Vec::new();

    let tcx = state.tcx;
    let ids = get_def_ids(tcx);

    let (mono_items, _) = collector::collect_crate_mono_items(tcx, MonoItemCollectionMode::Lazy);

    for mono_item in mono_items {
        let (inst, def_id, substs) = match mono_item {
            MonoItem::Fn(inst) => {
                let def_id = match inst.def {
                    ty::InstanceDef::Item(def_id) => def_id,
                    _ => continue,
                };
                (Some(inst), def_id, inst.substs)
            },
            MonoItem::Static(def_id) => {
                (None, def_id, ty::List::empty())
            },
            MonoItem::GlobalAsm(_) => continue,
        };

        let name = inst_id_str(tcx, def_id, substs);
        let mut mir = tcx.optimized_mir(def_id).clone();
        subst_const_tys(tcx, substs, &mut mir);
        let mir = tcx.subst_and_normalize_erasing_regions(
            substs, ty::ParamEnv::reveal_all(), &mir);
        let mir = tcx.arena.alloc(mir);

        state.session.note_without_error(&format!("Emitting MIR for {}", name));

        let mut ms = MirState {
            mir: Some(mir),
            used: used,
            state: state,
        };
        let fn_json = build_mir(&mut ms, &mut fns, &mut statics, &name, inst, mir);
        fns.push(fn_json);
    }

    (fns, statics)
}

pub fn emit_adts(state: &mut CompileState, used_types: &HashSet<DefId>, file: &mut File) -> io::Result<()> {
    let tcx = state.tcx;
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(None)?;
    let mut dummy_used = Used::default();

    // Emit definitions for all ADTs.
    for &def_id in used_types.iter() {
        if def_id.is_local() {
            let ty = tcx.type_of(def_id);
            match ty.ty_adt_def() {
                Some(adtdef) => {
                    let adt_name = def_id_str(tcx, def_id);
                    state.session.note_without_error(
                        format!("Emitting ADT definition for {}",
                                adt_name).as_str());
                    let mut ms = MirState {
                        mir: None,
                        used: &mut dummy_used,
                        state: state,
                    };
                    seq.serialize_element(&adtdef.tojson(&mut ms,
                                                         List::empty()))?;
                }
                _ => ()
            }
        } // Else look it up somewhere else, but I'm not sure where.
    }
    seq.end()?;
    Ok(())
}

pub fn emit_vtables<'tcx>(
    state: &mut CompileState<'_, 'tcx>,
    used_vtables: &HashSet<ty::PolyTraitRef<'tcx>>,
    file: &mut File,
) -> io::Result<()> {
    let tcx = state.tcx;
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(None)?;
    let mut dummy_used = Used::default();

    let mut ms = MirState {
        mir: None,
        used: &mut dummy_used,
        state: state,
    };

    // Emit definitions for all ADTs.
    for &trait_ref in used_vtables.iter() {
        seq.serialize_element(&json!({
            "name": vtable_name(&mut ms, trait_ref),
            "desc": trait_ref.skip_binder().to_json(&mut ms),
            "items": build_vtable_items(&mut ms, trait_ref),
        }))?;
    }
    seq.end()?;
    Ok(())
}

fn iter_trait_def_ids<'tcx>(
    state: &mut CompileState<'_, 'tcx>
) -> impl Iterator<Item=DefId> + 'tcx {
    let hir_map = state.tcx.hir();
    hir_map.krate().items.values()
        .filter(|it| match it.node {
            hir::ItemKind::Trait(..) => true,
            _ => false,
        })
        .map(|it| it.hir_id.owner_def_id())
}

fn iter_impl_def_ids<'tcx>(
    state: &mut CompileState<'_, 'tcx>
) -> impl Iterator<Item=DefId> + 'tcx {
    let hir_map = state.tcx.hir();
    hir_map.krate().items.values()
        .filter(|it| match it.node {
            hir::ItemKind::Impl(..) => true,
            _ => false,
        })
        .map(|it| it.hir_id.owner_def_id())
}

pub fn emit_traits(state: &mut CompileState, file: &mut File) -> io::Result<()> {
    let tcx = state.tcx;
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(None)?;
    let mut dummy_used = Used::default();

    // Emit definitions for all traits.
    for def_id in iter_trait_def_ids(state) {
        if !def_id.is_local() {
            continue;
        }
        if !tcx.is_object_safe(def_id) {
            continue;
        }

        let trait_name = def_id_str(tcx, def_id);
        let items = tcx.associated_items(def_id);
        state.session.note_without_error(
            format!("Emitting trait items for {}",
                    trait_name).as_str());
        let mut ms = MirState {
            mir: None,
            used: &mut dummy_used,
            state: state,
        };
        let mut items_json = Vec::new();
        for item in items {
            if !tcx.is_vtable_safe_method(def_id, &item) {
                continue;
            }
            items_json.push(assoc_item_json(&mut ms, tcx, &item));
        }
        let supers = traits::supertrait_def_ids(tcx, def_id);
        let mut supers_json = Vec::new();
        for item in supers {
            supers_json.push(item.to_json(&mut ms));
        }
        let preds = tcx.predicates_of(def_id);
        let generics = tcx.generics_of(def_id);
        seq.serialize_element(
            &json!({
                "name": def_id.to_json(&mut ms),
                "items": serde_json::Value::Array(items_json),
                "supertraits": serde_json::Value::Array(supers_json),
                "generics": generics.to_json(&mut ms),
                "predicates": preds.to_json(&mut ms),
            })
        )?;
    }
    seq.end()?;
    Ok(())
}

pub fn emit_impls(state: &mut CompileState, file: &mut File) -> io::Result<()> {
    let tcx = state.tcx;
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(None)?;
    let mut dummy_used = Used::default();

    for def_id in iter_impl_def_ids(state) {
        if !def_id.is_local() {
            // We only emit impls for the current crate.
            continue;
        }

        let trait_ref = match tcx.impl_trait_ref(def_id) {
            Some(x) => x,
            // Currently we don't bother emitting inherent impls.
            None => continue,
        };
        if !tcx.is_object_safe(trait_ref.def_id) {
            continue;
        }

        let preds = tcx.predicates_of(def_id);
        let generics = tcx.generics_of(def_id);

        let mut ms = MirState {
            mir: None,
            used: &mut dummy_used,
            state: state,
        };

        let items = tcx.associated_items(def_id);
        let mut items_json = Vec::new();
        for item in items {
            let trait_assoc_item = trait_item_for_impl_item(tcx, &item)
                .unwrap_or_else(|| panic!("can't find trait item for {:?}", item));
            if !tcx.is_vtable_safe_method(trait_ref.def_id, &trait_assoc_item) {
                continue;
            }
            items_json.push(assoc_item_json(&mut ms, tcx, &item));
        }

        seq.serialize_element(
            &json!({
                "name": def_id.to_json(&mut ms),
                "trait_ref": trait_ref.to_json(&mut ms),
                "generics": generics.to_json(&mut ms),
                "predicates": preds.to_json(&mut ms),
                "items": serde_json::Value::Array(items_json),
            })
        )?;
    }
    seq.end()?;
    Ok(())
}

pub fn analyze(comp: &Compiler) -> io::Result<()> {
    let iname = source_name(comp.input()).to_string();
    let mut mirname = Path::new(&iname).to_path_buf();
    mirname.set_extension("mir");
    let mut file = File::create(&mirname)?;

    let mut gcx = comp.global_ctxt().unwrap().peek_mut();
    gcx.enter(|tcx| {
        let mut used = Used::default();
        let mut state = CompileState {
            session: comp.session(),
            tcx,
        };
        {
            let (fns, statics) = emit_mono_items(&mut state, &mut used);
            write!(file, "{{ \"fns\": ")?;
            fns.serialize(&mut serde_json::Serializer::new(&mut file))?;
            write!(file, ", \"statics\": ")?;
            statics.serialize(&mut serde_json::Serializer::new(&mut file))?;
        }
        write!(file, ", \"adts\": ")?;
        emit_adts(&mut state, &used.types, &mut file)?;
        write!(file, ", \"vtables\": ")?;
        emit_vtables(&mut state, &used.vtables, &mut file)?;
        write!(file, ", \"traits\": ")?;
        emit_traits(&mut state, &mut file)?;
        write!(file, ", \"impls\": [] ")?;
        //emit_impls(&mut state, &mut file)?;
        write!(file, " }}")
    })
}

// format:
// top: function name || function args || return ty || body
// args: name || type || scope || mutability
// body: all locals || all basicblocks
// basicblock: all statements || terminator
