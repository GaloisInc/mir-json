import { DefId, Ty, Var, Mutability } from "common"
import { NullOp, UnOp, BinOp } from "operator"
import { Adt } from "adt"
import { Constant } from "constant"

type Lvalue = {
  var: Var, data: PlaceElem[]
}

type PlaceElem =
    { kind: "Deref" }
  | { kind: "Field", field: number, ty: Ty }
  | { kind: "Index", op: Var } 
  | { kind: "ConstantIndex", offset: number, min_length: number, from_end: boolean }
  | { kind: "Subslice", from: number, to: number, from_end: boolean }
  | { kind: "Downcast", variant: number }
  | { kind: "Subtype", ty: Ty }

type Rvalue =
    { kind: "Use", usevar: Operand }
  | { kind: "Repeat", op: Operand, len: number }
  | { kind: "Ref", borrowkind: BorrowKind, refvar: Lvalue, region: string }
  | { kind: "AddressOf", mutbl: Mutability, place: Lvalue }
  | { kind: "Len", lv: Lvalue }
  | { kind: "Cast", type: CastKind, op: Operand, ty: Ty }
  | { kind: "BinaryOp", op: BinOp, L: Operand, R: Operand }
  | { kind: "NullaryOp", op: NullOp, ty: Ty }
  | { kind: "UnaryOp", uop: UnOp, op: Operand }
  | { kind: "Discriminant", val: Lvalue, ty: Ty }
  | { kind: "Aggregate", akind: AggregateKind, ops: Operand[] }
  | { kind: "AdtAg", ag: AdtAg }
  | { kind: "ShallowInitBox", ptr: Operand, ty: Ty }
  | { kind: "CopyForDeref", place: Lvalue }
  | { kind: "ThreadLocalRef", def_id: DefId, ty: Ty }

type AdtAg = {
  adt: Adt,
  variant: number,
  ops: Operand[],
  ty: Ty,
  field: number?
}

type Operand =
    { kind: "Move", data: Lvalue }
  | { kind: "Constant", data: Constant }
  | { kind: "Copy", data: Lvalue }
  
type AggregateKind = 
    { kind: "Array", ty: Ty }
  | { kind: "Tuple" | "Closure" | "Coroutine" }
  | { kind: "RawPtr", ty: Ty, mutbl: Mutability }

type BorrowKind = "Shared" | "Unique" | "Mut"

type CastKind =
    { kind:
        "PointerExposeProvenance" |
        "PointerWithExposedProvenance" |
        "DynStar" |
        "IntToInt" |
        "FloatToInt" |
        "FloatToFloat" |
        "IntToFloat" |
        "PtrToPtr" |
        "FnPtrToPtr" |
        "Transmute"
    }
    |
    {
      kind: "PointerCoercion",
      origin: any,
      cast: { kind: "ReifyFnPointer" |
                    "UnsafeFnPointer" |
                    "MutToConstPointer" |
                    "ArrayToPointer" |
                    "Unsize" }
    }
    | { kind: "UnsizeVtable", vtable: DefId }
    | { kind: "ClosureFnPointer", shim: DefId }