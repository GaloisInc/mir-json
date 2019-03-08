#![macro_use]

use rustc::ty::{TyCtxt, List, TyS};
use rustc::mir::{self, Mir};
use rustc::hir::def_id;
use rustc::hir::def_id::DefId;
use rustc::traits;
use rustc_driver::driver::{CompileState, source_name};
use std::collections::HashSet;
use std::fmt::Write as FmtWrite;
use std::io;
use std::io::Write;
use std::fs::File;
use std::path::Path;
use serde::ser::{Serializer, SerializeSeq};
use serde_json;

#[macro_use]
mod to_json;
mod ty_json;
use analyz::to_json::*;
use analyz::ty_json::*;

basic_json_impl!(mir::Promoted);
basic_json_enum_impl!(mir::BinOp);

basic_json_enum_impl!(mir::NullOp);
basic_json_enum_impl!(mir::UnOp);

//basic_json_impl!(layout::VariantIdx);

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
                json!({
                    "kind": "Cast",
                    "type": ck.to_json(mir),
                    "op": op.to_json(mir),
                    "ty": ty.to_json(mir)
                })
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

impl<'tcx> ToJson<'tcx> for mir::Projection<'tcx, mir::Place<'tcx>, mir::Local, &'tcx TyS<'tcx>> {
    fn to_json(&self, mir: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        json!({
            "base": self.base.to_json(mir),
            "data" : self.elem.to_json(mir)
        })
    }
}

impl<'tcx, T: ToJson<'tcx>> ToJson<'tcx> for mir::ProjectionElem<'tcx, mir::Local, T> {
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
                json!({"kind": "Downcast", "variant": variant/*.to_json(mir)*/})
            }
        }
    }
}

impl<'tcx> ToJson<'tcx> for mir::Place<'tcx> {
    fn to_json(&self, ms: &mut MirState<'_, 'tcx>) -> serde_json::Value {
        match self {
            &mir::Place::Local(ref l) => {
                json!({"kind": "Local", "localvar": local_json(ms, *l) })
            }
            &mir::Place::Static(_) => {
                json!({"kind": "Static"}) // UNUSED
            }
            &mir::Place::Projection(ref p) => {
                json!({"kind": "Projection", "data" : p.to_json(ms)})
            }
            &mir::Place::Promoted(ref p) => {
                json!({"kind": "Promoted", "data" : p.to_json(ms)})
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
            &mir::StatementKind::SetDiscriminant {
                ref place,
                ref variant_index,
            } => {
                json!({
                    "kind": "SetDiscriminant",
                    "lvalue": place.to_json(mir),
                    "variant_index": variant_index/*.to_json(mir)*/
                })
            }
            &mir::StatementKind::StorageLive(l) => {
                json!({"kind": "StorageLive", "slvar": local_json(mir, l)})
            }
            &mir::StatementKind::StorageDead(l) => {
                json!({"kind": "StorageDead", "sdvar": local_json(mir, l)})
            }
            &mir::StatementKind::Nop => {
                json!({"kind": "Nop"})
            }
            &mir::StatementKind::EndRegion(_) => {
                // TODO
                json!({"kind": "EndRegion"})
            }
            &mir::StatementKind::Validate(..) => {
                // TODO
                json!({"kind": "Validate"})
            }
            &mir::StatementKind::InlineAsm { .. } => {
                // TODO
                json!({"kind": "InlineAsm"})
            }
            &mir::StatementKind::FakeRead { .. } => {
                // TODO
                json!({"kind": "FakeRead "})
            }
            &mir::StatementKind::AscribeUserType { .. } => {
                // TODO
                json!({"kind": "AscribeUserType"})
            }
            /*
            &mir::StatementKind::Retag { .. } => {
                // TODO
                json!({"kind": "Retag"})
            }
            */
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

pub fn get_mir<'tcx>(tcx: TyCtxt<'_, 'tcx, 'tcx>, id: DefId) -> Option<&'tcx Mir<'tcx>> {
    tcx.maybe_optimized_mir(id)
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
    _def_id: DefId,
    _tcx: &TyCtxt,
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

fn mir_info<'tcx>(
    ms: &mut MirState<'_, 'tcx>,
    def_id: DefId,
    tcx: &TyCtxt<'_, 'tcx, 'tcx>,
) -> Option<serde_json::Value> {
    let fn_name = tcx.def_path(def_id).to_string_no_crate();

    let mut args = Vec::new();
    for (_, local) in ms.mir.unwrap().args_iter().enumerate() {
        args.push(local_json(ms, local));
    }

    // name
    // input vars
    // output
    let body = mir_body(ms, def_id, tcx);
    let preds = tcx.predicates_of(def_id);
    let generics = tcx.generics_of(def_id);

    Some(
        json!({
            "name": fn_name,
            "args": args,
            "return_ty": ms.mir.unwrap().return_ty().to_json(ms),
            "generics": generics.to_json(ms),
            "predicates": preds.to_json(ms),
            "body": body
        })
    )

}

pub fn emit_fns(
    state: &mut CompileState,
    used_types: &mut HashSet<DefId>,
    file: &mut File
) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let ids = get_def_ids(tcx);
    let size = ids.len();
    let mut n = 1;
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(Some(size))?;

    for def_id in ids {
        let mir = get_mir(tcx, def_id);
        let fn_name = tcx.def_path(def_id).to_string_no_crate();
        let mut ms = MirState { mir: Some(mir.unwrap()),
                                used_types: used_types,
                                state: state };
        if let Some(mi) = mir_info(&mut ms, def_id, &tcx) {
            state.session.note_without_error(
                format!("Emitting MIR for {} ({}/{})",
                        fn_name,
                        n,
                        size).as_str());
            seq.serialize_element(&mi)?;
        }
        n = n + 1;
    }
    seq.end()?;
    Ok(())
}

pub fn emit_adts(state: &mut CompileState, used_types: &HashSet<DefId>, file: &mut File) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(None)?;
    let mut dummy_used_types = HashSet::new();

    // Emit definitions for all ADTs.
    for &def_id in used_types.iter() {
        if def_id.is_local() {
            let ty = tcx.type_of(def_id);
            match ty.ty_adt_def() {
                Some(adtdef) => {
                    let adt_name = tcx.def_path(def_id).to_string_no_crate();
                    state.session.note_without_error(
                        format!("Emitting ADT definition for {}",
                                adt_name).as_str());
                    let mut ms = MirState { mir: None,
                                            used_types: &mut dummy_used_types,
                                            state: state };
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

pub fn emit_traits(state: &mut CompileState, file: &mut File) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let mut ser = serde_json::Serializer::new(file);
    let mut seq = ser.serialize_seq(None)?;
    let mut dummy_used_types = HashSet::new();
    let traits = &*tcx.all_traits(def_id::LOCAL_CRATE);

    // Emit definitions for all traits.
    for &def_id in traits.iter() {
        if def_id.is_local() {
            let trait_name = tcx.def_path(def_id).to_string_no_crate();
            let items = tcx.associated_items(def_id);
            state.session.note_without_error(
                format!("Emitting trait items for {}",
                        trait_name).as_str());
            let mut ms = MirState { mir: None,
                                    used_types: &mut dummy_used_types,
                                    state: state };
            let mut items_json = Vec::new();
            for item in items {
                items_json.push(assoc_item_json(&mut ms, &tcx, &item));
            }
            let supers = traits::supertrait_def_ids(tcx, def_id);
            let mut supers_json = Vec::new();
            for item in supers {
                supers_json.push(item.to_json(&mut ms));
            }
            seq.serialize_element(
                &json!({
                    "name": def_id.to_json(&mut ms),
                    "items": serde_json::Value::Array(items_json),
                    "supertraits": serde_json::Value::Array(supers_json)
                })
            )?;
        } // Else look it up somewhere else, but I'm not sure where.
    }
    seq.end()?;
    Ok(())
}

pub fn analyze(state: &mut CompileState) -> io::Result<()> {
    let iname = source_name(state.input).to_string();
    let mut mirname = Path::new(&iname).to_path_buf();
    mirname.set_extension("mir");
    let mut file = File::create(&mirname)?;
    let mut used_types = HashSet::new();
    write!(file, "{{ \"fns\": ")?;
    emit_fns(state, &mut used_types, &mut file)?;
    write!(file, ", \"adts\": ")?;
    emit_adts(state, &used_types, &mut file)?;
    write!(file, ", \"traits\": ")?;
    emit_traits(state, &mut file)?;
    write!(file, " }}")
}

// format:
// top: function name || function args || return ty || body
// args: name || type || scope || mutability
// body: all locals || all basicblocks
// basicblock: all statements || terminator
