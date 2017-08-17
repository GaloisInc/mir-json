use rustc::ty::{self, TyCtxt};
use rustc::mir::{self, Mir};
use rustc::mir::transform::MirSource;
use rustc::hir::{self, def_id};
use rustc_data_structures::indexed_vec::Idx;
use rustc::middle;
use rustc::hir::def_id::DefId;
use syntax::{self, ast};
use rustc_driver::driver::CompileState;
use rustc_const_math;
use std::fmt::Write as FmtWrite;
use serde_json;
mod adt;



trait ToJson {
    fn to_json(&self, mir: &Mir) -> serde_json::Value;
}

impl ToJson for String {
    fn to_json(&self, _: &Mir) -> serde_json::Value {
        json!(self)
    }
}

impl<T> ToJson for Option<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &Some(ref i) => i.to_json(mir),
            &None => json!("null"),
        }
    }
}


macro_rules! basic_json_impl {
    ($n : path) => {
        impl ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!(s)
    }
}

};
}

macro_rules! basic_json_enum_impl {
    ($n : path) => {
        impl ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}
};
    ($n : path, $lt : tt) => {
        impl<$lt> ToJson for $n {
    fn to_json(&self, _ : &Mir) -> serde_json::Value {
        let mut s = String::new();
        write!(&mut s, "{:?}", self).unwrap();
        json!({"kind": s})
    }
}

};
}

impl<A, B> ToJson for (A, B)
where
    A: ToJson,
    B: ToJson,
{
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        let &(ref a, ref b) = self;
        json!(vec![a.to_json(mir), b.to_json(mir)])
    }
}

impl<T> ToJson for ty::Slice<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}


impl<T> ToJson for Vec<T>
where
    T: ToJson,
{
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        let mut j = Vec::new();
        for v in self {
            j.push(v.to_json(mir));
        }
        json!(j)
    }
}

impl ToJson for ast::IntTy {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &ast::IntTy::Is => json!("USize"),
            &ast::IntTy::I8 => json!("8"),
            &ast::IntTy::I16 => json!("16"),
            &ast::IntTy::I32 => json!("32"),
            &ast::IntTy::I64 => json!("64"),
            &ast::IntTy::I128 => json!("128"),
        }
    }
}

impl ToJson for ast::UintTy {
    fn to_json(&self, _: &Mir) -> serde_json::Value {
        match self {
            &ast::UintTy::Us => json!("USize"),
            &ast::UintTy::U8 => json!("8"),
            &ast::UintTy::U16 => json!("16"),
            &ast::UintTy::U32 => json!("32"),
            &ast::UintTy::U64 => json!("64"),
            &ast::UintTy::U128 => json!("128"),
        }
    }
}

impl ToJson for hir::Mutability {
    fn to_json(&self, _: &Mir) -> serde_json::Value {
        json!(match self {
            &hir::Mutability::MutMutable => "mut",
            _ => "immut",
        })
    }
}
impl ToJson for mir::Mutability {
    fn to_json(&self, _: &Mir) -> serde_json::Value {
        json!(match self {
            &mir::Mutability::Mut => "mut",
            _ => "immut",
        })
    }
}


impl<'a> ToJson for ty::Ty<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {

        match &self.sty {
            &ty::TypeVariants::TyBool => json!({"kind": "Bool"}),
            &ty::TypeVariants::TyChar => json!({"kind": "Char"}),
            &ty::TypeVariants::TyInt(ref t) => json!({"kind": "Int", "intkind": t.to_json(mir)}),
            &ty::TypeVariants::TyUint(ref t) => json!({"kind": "Uint", "uintkind": t.to_json(mir)}),
            &ty::TypeVariants::TyTuple(sl, _) => json!({"kind": "Tuple", "tys": sl.to_json(mir)}),
            &ty::TypeVariants::TySlice(ref f) => json!({"kind": "Slice", "ty": f.to_json(mir)}),
            &ty::TypeVariants::TyArray(ref t, ref size) => {
                json!({"kind": "Array", "ty": t.to_json(mir), "size": size})
            }
            &ty::TypeVariants::TyRef(ref region, ref tm) => {
                json!({"kind": "ref", "ty": tm.ty.to_json(mir), "mutability": tm.mutbl.to_json(mir)})
            }
            &ty::TypeVariants::TyAdt(ref adtdef, ref substs) => {
                if adt::is_custom(adtdef) {
                    json!({"kind": "custom", "data": adt::handle_adt_custom(mir, adtdef, substs)})
                } else {
                    json!({"kind": "adt", "adt": adt::handle_adt(mir, adtdef, substs)})
                }
            }
            &ty::TypeVariants::TyFnDef(defid, ref substs) => {
                json!({"kind": "fndef", "defid": defid.to_json(mir), "substs": substs.to_json(mir)})
            }
            &ty::TypeVariants::TyParam(ref p) => json!({"kind": "param", "param": p.to_json(mir)}),
            &ty::TypeVariants::TyClosure(ref defid, ref closuresubsts) => {
                json!({"kind": "closure", "defid": defid.to_json(mir), "closuresubsts": closuresubsts.substs.to_json(mir)})
            }
            _ => panic!(format!("type unsupported: {:?}", &self.sty)),
        }
    }
}

impl ToJson for ty::ParamTy {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!(self.idx)
    }
}



basic_json_enum_impl!(mir::CastKind);
basic_json_enum_impl!(mir::BorrowKind);

impl ToJson for rustc_const_math::ConstUsize {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!(self.as_u64(ast::UintTy::U64))
    }
}

impl ToJson for hir::def_id::DefId {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!(ty::tls::with(|tx| {
            let defpath = tx.def_path(*self);
            defpath.to_string_no_crate()
        }))
    }
}


basic_json_impl!(mir::Promoted);
basic_json_enum_impl!(mir::BinOp);


basic_json_enum_impl!(mir::NullOp);
basic_json_enum_impl!(mir::UnOp);

impl<'a> ToJson for mir::AggregateKind<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::AggregateKind::Array(ty) => json!({"kind": "array", "ty": ty.to_json(mir)}),
            &mir::AggregateKind::Tuple => json!({"kind": "tuple"}),
            &mir::AggregateKind::Adt(ref adtdef, _, _, _) => {
                panic!("adt should be handled upstream")
            }
            &mir::AggregateKind::Closure(ref defid, ref closuresubsts) => {
                json!({"kind": "agclosure", "defid": defid.to_json(mir), "closuresubsts": closuresubsts.substs.to_json(mir)})
            }
        }
    }
}




impl<'a> ToJson for middle::const_val::ConstVal<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &middle::const_val::ConstVal::Integral(i) if !(i.is_negative()) => {
                json!({"kind": "int", "data": i.to_u64().unwrap()})
            }
            &middle::const_val::ConstVal::Bool(b) => json!({"kind": "bool", "data": b}),
            &middle::const_val::ConstVal::Function(defid, substs) => {
                json!({"kind": "function", "fname": defid.to_json(mir), "substs": substs.to_json(mir)})
            }
            &middle::const_val::ConstVal::Array(ref constvals) => {
                json!({"kind": "array", "data": constvals.to_json(mir)})
            }
            _ => panic!("other const types unsupport"),
        }
    }
}


impl<'a> ToJson for mir::Rvalue<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::Rvalue::Use(ref op) => json!({"kind": "use", "usevar": op.to_json(mir)}),
            &mir::Rvalue::Repeat(ref op, ref s) => {
                json!({"kind": "repeat", "op": op.to_json(mir), "len": s.to_json(mir)})
            }
            &mir::Rvalue::Ref(_, ref bk, ref l) => {
                json!({"kind": "ref", "region": "unimplement", "borrowkind": bk.to_json(mir), "refvar": l.to_json(mir)})
            } // UNUSED
            &mir::Rvalue::Len(ref l) => json!({"kind": "len", "lv": l.to_json(mir)}),
            &mir::Rvalue::Cast(ref ck, ref op, ref ty) => {
                json!({"kind": "cast", "type": ck.to_json(mir), "op": op.to_json(mir), "ty": ty.to_json(mir)})
            }
            &mir::Rvalue::BinaryOp(ref binop, ref op1, ref op2) => {
                json!({"kind": "binaryop", "op": binop.to_json(mir), "L": op1.to_json(mir), "R": op2.to_json(mir)})
            }
            &mir::Rvalue::CheckedBinaryOp(ref binop, ref op1, ref op2) => {
                json!({"kind": "checkedbinaryop", "op": binop.to_json(mir), "L": op1.to_json(mir), "R": op2.to_json(mir)})
            }
            &mir::Rvalue::NullaryOp(ref no, ref t) => {
                json!({"kind": "nullaryop", "op": no.to_json(mir), "ty": t.to_json(mir)})
            }
            &mir::Rvalue::UnaryOp(ref uo, ref o) => {
                json!({"kind": "unaryop", "uop": uo.to_json(mir), "op": o.to_json(mir)})
            }
            &mir::Rvalue::Discriminant(ref lv) => {
                json!({"kind": "discriminant", "val": lv.to_json(mir)})
            }
            &mir::Rvalue::Aggregate(ref ak, ref opv) => {
                if adt::is_adt_ak(ak) {
                    json!({"kind": "adtag", "ag": adt::handle_adt_ag (mir, ak, opv)})
                } else {
                    json!({"kind": "aggregate", "akind": ak.to_json(mir), "ops": opv.to_json(mir)})
                }
            }
        }
    }
}


impl<'a> ToJson for mir::LvalueProjection<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!({"base": self.base.to_json(mir), "data" : self.elem.to_json(mir)})
    }
}

impl<'a, T: ToJson> ToJson for mir::ProjectionElem<'a, mir::Operand<'a>, T> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::ProjectionElem::Deref => json!({"kind": "deref"}),
            &mir::ProjectionElem::Field(ref f, ref ty) => {
                json!({"kind": "field", "field": f.to_json(mir), "ty": ty.to_json(mir)})
            }
            &mir::ProjectionElem::Index(ref op) => json!({"kind": "index", "op": op.to_json(mir)}),
            &mir::ProjectionElem::ConstantIndex {
                ref offset,
                ref min_length,
                ref from_end,
            } => {
                json!({"kind": "constantindex", "offset": offset, "min_length": min_length, "from_end": from_end})
            }
            &mir::ProjectionElem::Subslice { ref from, ref to } => {
                json!({"kind": "subslice", "from": from, "to": to})
            }
            &mir::ProjectionElem::Downcast(ref adt, ref variant) => {
                json!({"kind": "downcast", "variant": variant})
            }
        }
    }
}



impl<'a> ToJson for mir::Lvalue<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::Lvalue::Local(ref l) => {
                json!({"kind": "local", "localvar": local_json(mir, *l) })
            }
            &mir::Lvalue::Static(_) => json!({"kind": "static"}), // UNUSED
            &mir::Lvalue::Projection(ref p) => {
                json!({"kind": "projection", "data" : p.to_json(mir)})
            }
        }
    }
}

basic_json_impl!(mir::BasicBlock);

impl ToJson for mir::Field {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!(self.index())
    }
}

basic_json_impl!(mir::VisibilityScope);

basic_json_impl!(mir::AssertMessage<'a>, 'a);


impl<'a> ToJson for mir::Literal<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::Literal::Item {
                ref def_id,
                ref substs,
            } => {
                json!({"kind": "item", "def_id": def_id.to_json(mir), "substs": substs.to_json(mir)})
            }
            &mir::Literal::Value { ref value } => {
                json!({"kind": "value", "value": value.to_json(mir)})
            }
            &mir::Literal::Promoted { ref index } => {
                json!({"kind": "promoted", "index": index.to_json(mir)})
            }
        }
    }
}

impl<'a> ToJson for mir::Operand<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::Operand::Consume(ref l) => json!({"kind": "consume", "data": l.to_json(mir)}),
            &mir::Operand::Constant(ref l) => json!({"kind": "constant", "data": l.to_json(mir)}),
        }
    }
}

impl<'a> ToJson for mir::Constant<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!({"ty": self.ty.to_json(mir), "literal": self.literal.to_json(mir)})
    }
}


impl<'a> ToJson for mir::LocalDecl<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        json!({"mut": self.mutability.to_json(mir), "ty": self.ty.to_json(mir), "scope": self.source_info.scope.to_json(mir)})
    }
}

impl<'a> ToJson for mir::Statement<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
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
            &mir::StatementKind::EndRegion(_) => json!({"kind": "EndRegion"}),
            _ => json!({"kind": "unrecognized"}),
        }

    }
}

impl<'a> ToJson for mir::TerminatorKind<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
        match self {
            &mir::TerminatorKind::Goto { ref target } => {
                json!({"kind": "goto", "target": target.to_json(mir)})
            }
            &mir::TerminatorKind::SwitchInt {
                ref discr,
                ref switch_ty,
                ref values,
                ref targets,
            } => {
                let vals: Vec<u64> = values.iter().map(|c| c.to_u64().unwrap()).collect();

                json!({"kind": "switchint", "discr": discr.to_json(mir), "switch_ty": switch_ty.to_json(mir), "values": vals, "targets": targets.to_json(mir)})
            }
            &mir::TerminatorKind::Resume => json!({"kind": "resume"}),
            &mir::TerminatorKind::Return => json!({"kind": "return"}),
            &mir::TerminatorKind::Unreachable => json!({"kind": "unreachable"}),
            &mir::TerminatorKind::Drop {
                ref location,
                ref target,
                ref unwind,
            } => {
                json!({"kind": "drop", "location": location.to_json(mir), "target" : target.to_json(mir), "unwind": unwind.to_json(mir)})
            }
            &mir::TerminatorKind::DropAndReplace {
                ref location,
                ref value,
                ref target,
                ref unwind,
            } => {
                json!({"kind": "dropandreplace", "location": location.to_json(mir), "value": value.to_json(mir), "target": target.to_json(mir), "unwind": unwind.to_json(mir)})
            }
            &mir::TerminatorKind::Call {
                ref func,
                ref args,
                ref destination,
                ref cleanup,
            } => {
                json!({"kind": "call", "func": func.to_json(mir), "args": args.to_json(mir), "destination": destination.to_json(mir), "cleanup": cleanup.to_json(mir)})
            }
            &mir::TerminatorKind::Assert {
                ref cond,
                ref expected,
                ref msg,
                ref target,
                ref cleanup,
            } => {
                json!({"kind": "assert", "cond": cond.to_json(mir), "expected": expected, "msg": msg.to_json(mir), "target": target.to_json(mir), "cleanup": cleanup.to_json(mir)})
            }
        }
    }
}



impl<'a> ToJson for mir::BasicBlockData<'a> {
    fn to_json(&self, mir: &Mir) -> serde_json::Value {
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
pub fn analyze(state: &mut CompileState) {
    let tcx = state.tcx.unwrap();

    let mut jsons = Vec::new();
    for def_id in get_def_ids(tcx) {
        let src = MirSource::from_node(tcx, tcx.hir.as_local_node_id(def_id).unwrap());
        if let Some(mi) = mir_info(get_mir(tcx, def_id).unwrap(), def_id, src, &tcx) {
            jsons.push(mi)
        }
    }

    println!("{}", json!(jsons));

}

pub fn local_json<'a, 'tcx>(mir: &Mir<'a>, local: mir::Local) -> serde_json::Value {
    let mut j = mir.local_decls[local].to_json(mir);
    let mut s = String::new();
    write!(&mut s, "{:?}", local).unwrap();
    j["name"] = json!(s);
    j
}

fn mir_info<'a, 'tcx>(
    mir: &Mir<'a>,
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
    for (_, local) in mir.args_iter().enumerate() {
        args.push(local_json(mir, local));
    }

    // name
    // input vars
    // output
    let body = mir_body(mir, def_id, src, tcx);

    Some(
        json!({"name": fn_name, "args": args, "return_ty": mir.return_ty.to_json(mir), "body": body}),
    )

}


fn mir_body<'a, 'tcx>(
    mir: &Mir<'a>,
    _def_id: DefId,
    _src: MirSource,
    _tcx: &TyCtxt<'a, 'tcx, 'tcx>,
) -> serde_json::Value {
    let mut vars = Vec::new();

    vars.push(local_json(mir, mir::RETURN_POINTER));


    for (_, v) in mir.vars_and_temps_iter().enumerate() {
        vars.push(local_json(mir, v));
    }

    let mut blocks = Vec::new();
    for bb in mir.basic_blocks().indices() {
        //blocks.push(json!({"name": bb.to_json(), "data":mir[bb].to_json()})); // if it turns out
        //theyre not in order
        blocks.push(
            json!({"blockid": bb.to_json(mir), "block": mir[bb].to_json(mir)}),
        );
    }
    json!({"vars": vars, "blocks": blocks})
}

// format:
// top: function name || function args || return ty || body
// args: name || type || scope || mutability
// body: all locals || all basicblocks
// basicblock: all statements || terminator
