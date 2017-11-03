#![macro_use]

use rustc::ty::{TyCtxt};
use rustc::mir::{self, Mir};
use rustc::mir::transform::MirSource;
use rustc::hir::def_id;
use rustc_data_structures::indexed_vec::Idx;
use rustc::middle;
use rustc::hir::def_id::DefId;
use rustc_const_math;
use rustc_driver::driver::{CompileState, source_name};
use std::collections::HashSet;
use std::fmt::Write as FmtWrite;
use std::io;
use std::io::Write;
use std::fs::File;
use std::path::Path;
use serde_json;

#[macro_use]
mod to_json;
mod ty_json;
use analyz::to_json::*;


basic_json_impl!(mir::Promoted);
basic_json_enum_impl!(mir::BinOp);

basic_json_enum_impl!(mir::NullOp);
basic_json_enum_impl!(mir::UnOp);

impl ToJson for rustc_const_math::ConstFloat {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        json!({"ty": self.ty.to_json(mir), "bits": "TODO" /*json!(self.bits)*/})
    }
}

impl ToJson for rustc_const_math::ConstUsize {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        match self {
            &rustc_const_math::Us16(n) => json!(n),
            &rustc_const_math::Us32(n) => json!(n),
            &rustc_const_math::Us64(n) => json!(n),
        }
    }
}

impl ToJson for rustc_const_math::ConstIsize {
    fn to_json(&self, _ : &mut MirState) -> serde_json::Value {
        match self {
            &rustc_const_math::Is16(n) => json!(n),
            &rustc_const_math::Is32(n) => json!(n),
            &rustc_const_math::Is64(n) => json!(n),
        }
    }
}

impl ToJson for rustc_const_math::ConstInt {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &rustc_const_math::I8(n) => json!({"kind": "i8", "val": json!(n)}),
            &rustc_const_math::I16(n) => json!({"kind": "i16", "val": json!(n)}),
            &rustc_const_math::I32(n) => json!({"kind": "i32", "val": json!(n)}),
            &rustc_const_math::I64(n) => json!({"kind": "i64", "val": json!(n)}),
            //&rustc_const_math::I128(n) => json!({"kind": "i128", "val": json!(n)}),
            &rustc_const_math::Isize(n) => json!({"kind": "isize", "val": n.to_json(mir)}),
            &rustc_const_math::U8(n) => json!({"kind": "u8", "val": json!(n)}),
            &rustc_const_math::U16(n) => json!({"kind": "u16", "val": json!(n)}),
            &rustc_const_math::U32(n) => json!({"kind": "u32", "val": json!(n)}),
            &rustc_const_math::U64(n) => json!({"kind": "u64", "val": json!(n)}),
            //&rustc_const_math::U128(n) => json!({"kind": "u128", "val": json!(n)}),
            &rustc_const_math::Usize(n) => json!({"kind": "usize", "val": n.to_json(mir)}),
            _ => panic!("const int not supported")
        }
    }
}

impl<'a> ToJson for mir::AggregateKind<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::AggregateKind::Array(ty) => json!({"kind": "Array", "ty": ty.to_json(mir)}),
            &mir::AggregateKind::Tuple => json!({"kind": "Tuple"}),
            &mir::AggregateKind::Adt(_, _, _, _) => {
                panic!("adt should be handled upstream")
            }
            &mir::AggregateKind::Closure(ref defid, ref closuresubsts) => {
                json!({"kind": "Closure", "defid": defid.to_json(mir), "closuresubsts": closuresubsts.substs.to_json(mir)})
            }
        }
    }
}

impl<'a> ToJson for middle::const_val::ConstVal<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &middle::const_val::ConstVal::Integral(i) => {
                json!({"kind": "Integral", "data": i.to_json(mir)})
            }
            &middle::const_val::ConstVal::Float(i) => {
                json!({"kind": "Float", "data": i.to_json(mir)})
            }
            &middle::const_val::ConstVal::Bool(b) => {
                json!({"kind": "Bool", "data": b})
            }
            &middle::const_val::ConstVal::Char(c) => {
                json!({"kind": "Char", "data": c})
            }
            &middle::const_val::ConstVal::Str(ref s) => {
                json!({"kind": "Str", "data": serde_json::Value::String(s.to_string())})
            }
            &middle::const_val::ConstVal::ByteStr(..) => {
                json!({"kind": "ByteStr"}) // TODO
            }
            &middle::const_val::ConstVal::Function(defid, substs) => {
                json!({"kind": "Function", "fname": defid.to_json(mir), "substs": substs.to_json(mir)})
            }
            &middle::const_val::ConstVal::Array(ref constvals) => {
                json!({"kind": "Array", "data": constvals.to_json(mir)})
            }
            &middle::const_val::ConstVal::Tuple(..) => {
                json!({"kind": "Tuple"}) // TODO
            }
            &middle::const_val::ConstVal::Variant(defid) => {
                json!({"kind": "Variant", "name": defid.to_json(mir)})
            }
            &middle::const_val::ConstVal::Struct(..) => {
                json!({"kind": "Struct"}) // TODO
            }
            &middle::const_val::ConstVal::Repeat(..) => {
                json!({"kind": "Repeat"}) // TODO
            }
        }
    }
}

impl<'a> ToJson for mir::Rvalue<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::Rvalue::Use(ref op) => json!({"kind": "Use", "usevar": op.to_json(mir)}),
            &mir::Rvalue::Repeat(ref op, ref s) => {
                json!({"kind": "Repeat", "op": op.to_json(mir), "len": s.to_json(mir)})
            }
            &mir::Rvalue::Ref(_, ref bk, ref l) => {
                json!({"kind": "Ref", "region": "unimplement", "borrowkind": bk.to_json(mir), "refvar": l.to_json(mir)})
            } // UNUSED
            &mir::Rvalue::Len(ref l) => json!({"kind": "Len", "lv": l.to_json(mir)}),
            &mir::Rvalue::Cast(ref ck, ref op, ref ty) => {
                json!({"kind": "Cast", "type": ck.to_json(mir), "op": op.to_json(mir), "ty": ty.to_json(mir)})
            }
            &mir::Rvalue::BinaryOp(ref binop, ref op1, ref op2) => {
                json!({"kind": "BinaryOp", "op": binop.to_json(mir), "L": op1.to_json(mir), "R": op2.to_json(mir)})
            }
            &mir::Rvalue::CheckedBinaryOp(ref binop, ref op1, ref op2) => {
                json!({"kind": "CheckedBinaryOp", "op": binop.to_json(mir), "L": op1.to_json(mir), "R": op2.to_json(mir)})
            }
            &mir::Rvalue::NullaryOp(ref no, ref t) => {
                json!({"kind": "NullaryOp", "op": no.to_json(mir), "ty": t.to_json(mir)})
            }
            &mir::Rvalue::UnaryOp(ref uo, ref o) => {
                json!({"kind": "UnaryOp", "uop": uo.to_json(mir), "op": o.to_json(mir)})
            }
            &mir::Rvalue::Discriminant(ref lv) => {
                json!({"kind": "Discriminant", "val": lv.to_json(mir)})
            }
            &mir::Rvalue::Aggregate(ref ak, ref opv) => {
                if ty_json::is_adt_ak(ak) {
                    json!({"kind": "AdtAg", "ag": ty_json::handle_adt_ag (mir, ak, opv)})
                } else {
                    json!({"kind": "Aggregate", "akind": ak.to_json(mir), "ops": opv.to_json(mir)})
                }
            }
        }
    }
}

impl<'a> ToJson for mir::LvalueProjection<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        json!({"base": self.base.to_json(mir), "data" : self.elem.to_json(mir)})
    }
}

impl<'a, T: ToJson> ToJson for mir::ProjectionElem<'a, mir::Operand<'a>, T> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::ProjectionElem::Deref => json!({"kind": "Deref"}),
            &mir::ProjectionElem::Field(ref f, ref ty) => {
                json!({"kind": "Field", "field": f.to_json(mir), "ty": ty.to_json(mir)})
            }
            &mir::ProjectionElem::Index(ref op) => json!({"kind": "Index", "op": op.to_json(mir)}),
            &mir::ProjectionElem::ConstantIndex {
                ref offset,
                ref min_length,
                ref from_end,
            } => {
                json!({"kind": "ConstantIndex", "offset": offset, "min_length": min_length, "from_end": from_end})
            }
            &mir::ProjectionElem::Subslice { ref from, ref to } => {
                json!({"kind": "Subslice", "from": from, "to": to})
            }
            &mir::ProjectionElem::Downcast(ref _adt, ref variant) => {
                json!({"kind": "Downcast", "variant": variant})
            }
        }
    }
}

impl<'a> ToJson for mir::Lvalue<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::Lvalue::Local(ref l) => {
                json!({"kind": "Local", "localvar": local_json(mir, *l) })
            }
            &mir::Lvalue::Static(_) => json!({"kind": "Static"}), // UNUSED
            &mir::Lvalue::Projection(ref p) => {
                json!({"kind": "Projection", "data" : p.to_json(mir)})
            }
        }
    }
}

basic_json_impl!(mir::BasicBlock);

impl ToJson for mir::Field {
    fn to_json(&self, _mir: &mut MirState) -> serde_json::Value {
        json!(self.index())
    }
}

basic_json_impl!(mir::VisibilityScope);

basic_json_impl!(mir::AssertMessage<'a>, 'a);

impl<'a> ToJson for mir::Literal<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::Literal::Item {
                ref def_id,
                ref substs,
            } => {
                json!({"kind": "Item", "def_id": def_id.to_json(mir), "substs": substs.to_json(mir)})
            }
            &mir::Literal::Value { ref value } => {
                json!({"kind": "Value", "value": value.to_json(mir)})
            }
            &mir::Literal::Promoted { ref index } => {
                json!({"kind": "Promoted", "index": index.to_json(mir)})
            }
        }
    }
}

impl<'a> ToJson for mir::Operand<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match self {
            &mir::Operand::Consume(ref l) => json!({"kind": "Consume", "data": l.to_json(mir)}),
            &mir::Operand::Constant(ref l) => json!({"kind": "Constant", "data": l.to_json(mir)}),
        }
    }
}

impl<'a> ToJson for mir::Constant<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        json!({"ty": self.ty.to_json(mir), "literal": self.literal.to_json(mir)})
    }
}

impl<'a> ToJson for mir::LocalDecl<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        json!({"mut": self.mutability.to_json(mir), "ty": self.ty.to_json(mir), "scope": self.source_info.scope.to_json(mir)})
    }
}

impl<'a> ToJson for mir::Statement<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        match &self.kind {
            &mir::StatementKind::Assign(ref l, ref r) => {
                json!({"kind": "Assign", "lhs": l.to_json(mir), "rhs": r.to_json(mir)})
            }
            &mir::StatementKind::SetDiscriminant {
                ref lvalue,
                ref variant_index,
            } => {
                json!({"kind": "SetDiscriminant", "lvalue": lvalue.to_json(mir), "variant_index": variant_index})
            }
            &mir::StatementKind::StorageLive(ref l) => {
                json!({"kind": "StorageLive", "slvar": l.to_json(mir)})
            }
            &mir::StatementKind::StorageDead(ref l) => {
                json!({"kind": "StorageDead", "sdvar": l.to_json(mir)})
            }
            &mir::StatementKind::Nop => json!({"kind": "Nop"}),
            // TODO
            &mir::StatementKind::EndRegion(_) => json!({"kind": "EndRegion"}),
            // TODO
            &mir::StatementKind::Validate(..) => json!({"kind": "Validate"}),
            // TODO
            &mir::StatementKind::InlineAsm { .. } => json!({"kind": "InlineAsm"}),
        }

    }
}

impl<'a> ToJson for mir::TerminatorKind<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
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
                let vals: Vec<Option<u64>> = values.iter().map(|c| c.to_u64()).collect();

                json!({"kind": "SwitchInt", "discr": discr.to_json(mir), "switch_ty": switch_ty.to_json(mir), "values": vals, "targets": targets.to_json(mir)})
            }
            &mir::TerminatorKind::Resume => json!({"kind": "Resume"}),
            &mir::TerminatorKind::Return => json!({"kind": "Return"}),
            &mir::TerminatorKind::Unreachable => json!({"kind": "Unreachable"}),
            &mir::TerminatorKind::Drop {
                ref location,
                ref target,
                ref unwind,
            } => {
                json!({"kind": "Drop", "location": location.to_json(mir), "target" : target.to_json(mir), "unwind": unwind.to_json(mir)})
            }
            &mir::TerminatorKind::DropAndReplace {
                ref location,
                ref value,
                ref target,
                ref unwind,
            } => {
                json!({"kind": "DropAndReplace", "location": location.to_json(mir), "value": value.to_json(mir), "target": target.to_json(mir), "unwind": unwind.to_json(mir)})
            }
            &mir::TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ref cleanup,
            } => {
                json!({"kind": "Call", "func": func.to_json(mir), "args": args.to_json(mir), "destination": destination.to_json(mir), "cleanup": cleanup.to_json(mir)})
            }
            &mir::TerminatorKind::Assert {
                ref cond,
                ref expected,
                ref msg,
                ref target,
                ref cleanup,
            } => {
                json!({"kind": "Assert", "cond": cond.to_json(mir), "expected": expected, "msg": msg.to_json(mir), "target": target.to_json(mir), "cleanup": cleanup.to_json(mir)})
            }
        }
    }
}

impl<'a> ToJson for mir::BasicBlockData<'a> {
    fn to_json(&self, mir: &mut MirState) -> serde_json::Value {
        let mut sts = Vec::new();
        for statement in &self.statements {
            sts.push(statement.to_json(mir));
        }
        json!({"data": sts, "terminator": self.terminator().kind.to_json(mir)})
    }
}

pub fn get_def_ids(tcx: TyCtxt) -> Vec<DefId> {
    tcx.mir_keys(def_id::LOCAL_CRATE)
        .iter()
        .cloned()
        .collect::<Vec<_>>()
}

pub fn get_mir<'a, 'tcx>(tcx: TyCtxt<'a, 'tcx, 'tcx>, id: DefId) -> Option<&'a Mir<'a>> {
    tcx.maybe_optimized_mir(id).clone()
}

pub fn emit(state: &mut CompileState, file: &mut File) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let ids = get_def_ids(tcx);
    let size = ids.len();
    let mut n = 1;
    let mut adts = HashSet::new();

    for def_id in ids {
        let fn_name = tcx.def_path(def_id).to_string_no_crate();
        if !fn_name.contains("fmt") {
            state.session.note_without_error(format!("Emitting MIR for {} ({}/{})", fn_name, n, size).as_str());
            let src = MirSource::from_node(tcx, tcx.hir.as_local_node_id(def_id).unwrap());
            let mut ms = MirState { mir: get_mir(tcx, def_id).unwrap(),
                                    adts: &mut adts };
            if let Some(mi) = mir_info(&mut ms, def_id, src, &tcx) {
                write!(file, "{}", if n == 1 { "[" } else { "," })?;
                writeln!(file, "{}", mi)?;
                n = n + 1;
            }
        }
    }
    writeln!(file, "]")?;

    // Once bodies are emitted, also emit definitions for all ADTs.
    // Probably want to include traits here, eventually, too.
    for def_id in &adts {
        let ty = tcx.type_of(*def_id);
        match ty.ty_adt_def() {
            Some(adtdef) => {
                // TODO: emit it. This is slightly non-trivial because
                // the pretty-printer requires a Mir object. It won't
                // need it in this case, but the type of the trait
                // method requires it.
            }
            _ => ()
        }
    }
    Ok(())
}

pub fn analyze(state: &mut CompileState) -> io::Result<()> {
    let iname = source_name(state.input);
    let mut mirname = Path::new(&iname).to_path_buf();
    mirname.set_extension("mir");
    let mut file = File::create(&mirname)?;
    emit(state, &mut file)
}

pub fn local_json<'a, 'tcx>(ms: &mut MirState<'a>, local: mir::Local) -> serde_json::Value {
    let mut j = ms.mir.local_decls[local].to_json(ms);
    let mut s = String::new();
    write!(&mut s, "{:?}", local).unwrap();
    j["name"] = json!(s);
    j
}

fn mir_info<'a, 'tcx>(
    ms: &mut MirState<'a>,
    def_id: DefId,
    src: MirSource,
    tcx: &TyCtxt<'a, 'tcx, 'tcx>,
) -> Option<serde_json::Value> {
    match src {
        MirSource::Fn(_) => (),
        _ => return None,
    };
    let fn_name = tcx.def_path(def_id).to_string_no_crate();

    let mut args = Vec::new();
    for (_, local) in ms.mir.args_iter().enumerate() {
        args.push(local_json(ms, local));
    }

    // name
    // input vars
    // output
    let body = mir_body(ms, def_id, src, tcx);

    Some(
        json!({"name": fn_name, "args": args, "return_ty": ms.mir.return_ty.to_json(ms), "body": body}),
    )

}

fn mir_body<'a, 'tcx>(
    ms: &mut MirState<'a>,
    _def_id: DefId,
    _src: MirSource,
    _tcx: &TyCtxt<'a, 'tcx, 'tcx>,
) -> serde_json::Value {
    let mut vars = Vec::new();

    vars.push(local_json(ms, mir::RETURN_POINTER));

    for (_, v) in ms.mir.vars_and_temps_iter().enumerate() {
        vars.push(local_json(ms, v));
    }

    let mut blocks = Vec::new();
    for bb in ms.mir.basic_blocks().indices() {
        //blocks.push(json!({"name": bb.to_json(), "data":mir[bb].to_json()})); // if it turns out
        //theyre not in order
        blocks.push(
            json!({"blockid": bb.to_json(ms), "block": ms.mir[bb].to_json(ms)}),
        );
    }
    json!({"vars": vars, "blocks": blocks})
}

// format:
// top: function name || function args || return ty || body
// args: name || type || scope || mutability
// body: all locals || all basicblocks
// basicblock: all statements || terminator
