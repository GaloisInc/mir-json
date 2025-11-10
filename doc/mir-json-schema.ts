/*
This schema specifies the format of the JSON produced by `mir-json`.
The format is---more or less--just TypeScript types.  The full details
of the format are available at: https://github.com/GaloisInc/simple-json-schema
*/


/// The MIR JSON format
type MIR = {
  version: 5,
  fns: Fn[],
  adts: Adt[],
  statics: Static[],
  vtables: Vtable[],
  traits: Trait[],
  intrinsics: Intrinsic[],
  tys: NamedTy[],
  lang_items: LangItem[],
  roots: DefId[],
  tests: DefId[]
}

// -----------------------------------------------------------------------------
// Functions
// -----------------------------------------------------------------------------


/// Definition names
type DefId = string

/// Function definition
type Fn = {
  abi: Abi,
  name: string,
  args: Var[],
  body: MirBody,
  spread_arg: number?,
  return_ty: Ty
}

/// Calling convention for this function
type Abi = {
  kind: string,
  ...
}

type FnSig = {
  inputs: Ty[],
  output: Ty,
  abi: Abi
}

/// Variables
type Var = {
  /// Is this a zero size type?
  is_zst: boolean,
  mut: Mutability,
  name: string,
  ty: Ty
}

/// Mutability setttings
type Mutability = {
  kind: "MutMutable" | "Mut" | "MutImmutable" | "Not"
}

/// Implementation of a Rust function
type MirBody = {
  vars: Var[],
  blocks: BasicBlock[]
}

type BasicBlockInfo = string

type BasicBlock = {
  blockid: string,
  block: BasicBlockData
}

type BasicBlockData = {
  data: Statement[],
  terminator: Terminator
}




// -----------------------------------------------------------------------------
// ADTs
// -----------------------------------------------------------------------------

/// Algebraic datatypes
type Adt = {
  name: DefId,
  kind: AdtKind,
  variants: Variant[],
  size: number,
  repr_transparent: boolean,
  orig_def_id: DefId,
  orig_args: Ty[]
}

type AdtKind =
    { kind: "Struct" | "Union" }
  | { kind: "Enum", discr_ty: Ty }

type Variant = {
  name: DefId,
  discr: VariantDiscr,
  fields: Field[],
  ctor_kind: CtorKind?,
  discr_value: string?,
  inhabited: boolean
}

type VariantDiscr =
    { kind: "Explicit", name: DefId }
  | { kind: "Relative", index: number }

type Field = {
  name: DefId,
  ty: Ty
}

type CtorKind = {
  kind: "Fn" | "Const"
}



// -----------------------------------------------------------------------------
// Named Types
// -----------------------------------------------------------------------------

/// A named type
type Ty = string

/// Definition of a named type
type NamedTy = {
  name:   string,
  ty:     InlineType,
  layout: Layout?,
  needs_drop: boolean
}

type InlineType =
    { kind: "Bool" | "Char" | "Str" | "Never" | "Foreign" | "Coroutine" | "CoroutineWitness" }
  | { kind: "Int", intkind: BaseSize }
  | { kind: "Uint", uintkind: BaseSize }
  | { kind: "Tuple", tys: Ty[] }
  | { kind: "Array", size: Constant, ty: Ty }
  | { kind: "Ref", ty: Ty, mutability: Mutability }
  | { kind: "FnDef", defid: DefId }
  | { kind: "Adt", name: DefId, orig_def_id: DefId, args: Ty[] }
  | { kind: "Closure", upvar_tys: Ty[] }
  | { kind: "FnPtr", signature: FnSig }
  | { kind: "Dynamic", trait_id: DefId, predicates: any[] }
  | { kind: "RawPtr", ty: Ty, mutability: Mutability }
  | { kind: "Float", size: FloatKind }
  | { kind: "Slice", ty: Ty }
  | { kind: "Const", constant: ConstVal }

type BaseSize = {
  kind: "Usize" | "U8" | "U16" | "U32" | "U64" | "U128" |
        "Isize" | "I8" | "I16" | "I32" | "I64" | "I128"
}
            
type FloatKind = { kind: "F32" | "F64" }

type Layout = {
  align: number,
  size: number
}




// -----------------------------------------------------------------------------
// Globals
// -----------------------------------------------------------------------------

/// Globals
type Static = {
  kind: "constant" | "body",
  name: DefId,
  ty: Ty,
  mutable: boolean,
  rendered?: ConstVal
}


// -----------------------------------------------------------------------------
// Virtual Tables
// -----------------------------------------------------------------------------

type Vtable = {
  name : DefId,
  items: VtableItem[],
  trait_id: DefId
}

type VtableItem = {
  def_id: DefId,
  item_id: DefId
}


// -----------------------------------------------------------------------------
// Traits
// -----------------------------------------------------------------------------

type Trait = {
  name: DefId,
  items: TraitItem[]
}

type TraitItem = {
  kind: "Method",
  item_id: DefId,
  signature: FnSig
}


// -----------------------------------------------------------------------------
// Lang Items
// -----------------------------------------------------------------------------

type LangItem = {
  orig_def_id: DefId,
  name: DefId
}



// -----------------------------------------------------------------------------
// Instantiations
// -----------------------------------------------------------------------------

type Intrinsic = {
  name: DefId,
  inst: Instance
}

type Instance =
   { kind: "Item" | "Intrinsic" | "VtableShim" | "ReifyShim", def_id: DefId, args: Ty[] }
 | { kind: "FnPtrShim", ty: Ty, def_id: DefId, args: Ty[] }
 | { kind: "Virtual", trait_id: DefId, index: number, item_id: DefId }
 | { kind: "ClosureOnceShim", call_once: DefId, args: Ty[] }
 | { kind: "DropGlue", ty: Ty?, def_id: DefId, args: Ty?[] }
 | { kind: "ClosureShim", ty: Ty, callees: DefId[], def_id: DefId, args: Ty[] }
 | { kind: "ClosureFnPointerShim", call_mut: DefId }


// -----------------------------------------------------------------------------
// Constants
// -----------------------------------------------------------------------------

type Constant =
    { rendered: ConstVal, ty: Ty }
  | { initializer: RustConstInitializer, ty: Ty }

type RustConstInitializer = {
  def_id: DefId
}

type ConstVal =
    { kind: "isize", size: number,             val: string }
  | { kind: "int",   size: 1 | 2 | 4 | 8 | 16, val: string }
  | { kind: "usize", size: number,             val: string }
  | { kind: "uint",  size: 1 | 2 | 4 | 8 | 16, val: string }
  | { kind: "bool",  size: number,             val: "0" | "1" }
  | { kind: "char",  size: number,             val: string }
  | { kind: "float", size: 4 | 8,              val: string }
  | { kind: "slice", def_id: DefId, len: number }
  | { kind: "strbody", len: number, elements: number[] }
  | { kind: "struct",  fields: ConstVal[] }
  | { kind: "enum", variant: number, fields: ConstVal[] }
  | { kind: "union" }
  | { kind: "fndef", def_id: DefId }
  | { kind: "static_ref", def_id: DefId }
  | { kind: "zst" }
  | { kind: "raw_ptr", val: string }
  | { kind: "array", element_ty: Ty, elements: ConstVal[] }
  | { kind: "array", len: number, elements: ConstVal[] }
  | { kind: "tuple", elements: ConstVal[] }
  | { kind: "closure", upvars: ConstVal[] }
  | { kind: "fn_ptr", "def_id": DefId }





// -----------------------------------------------------------------------------
// Expressions
// -----------------------------------------------------------------------------

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

type NullOp = {
  kind: "SizeOf" | "AlignOf" | "UbChecks"
}

type UnOp = {
  kind: "Not" | "Neg" | "PtrMetadata"
}

type BinOp = {
  kind:
      "Add" | "AddUnchecked" | "AddWithOverflow"
    | "Sub" | "SubUnchecked" | "SubWithOverflow"
    | "Mul" | "MulUnchecked" | "MulWithOverflow"
    | "Div" | "Rem"
    | "BitXor" | "BitAnd" | "BitOr"
    | "Shl" | "ShlUnchecked" | "Shr" | "ShrUnchecked"
    | "Eq" | "Lt" | "Le" | "Ne" | "Ge" | "Gt"
    | "Offset" | "Cmp"
}

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
      { kind: "PointerExposeProvenance"
            | "PointerWithExposedProvenance"
            | "DynStar"
            | "IntToInt"
            | "FloatToInt"
            | "FloatToFloat"
            | "IntToFloat"
            | "PtrToPtr"
            | "FnPtrToPtr"
            | "Transmute" }
    | { kind: "PointerCoercion",
        origin: any,
        cast: { kind: "ReifyFnPointer"
                    | "UnsafeFnPointer"
                    | "MutToConstPointer"
                    | "ArrayToPointer"
                    | "Unsize" }
      }
    | { kind: "UnsizeVtable", vtable: DefId }
    | { kind: "ClosureFnPointer", shim: DefId }


// -----------------------------------------------------------------------------
// Statements
// -----------------------------------------------------------------------------

type Statement =
    { kind: "Assign", lhs: Lvalue, rhs: Rvalue, pos: string }
  | { kind: "SetDiscriminant", lvalue: Lvalue, variant_index: number, pos: string }
  | { kind: "StorageLive", slvar: Var, pos: string }
  | { kind: "StorageDead", sdvar: Var, pos: string }
  | { kind: "Nop", pos: string }
  | { kind: "Deinit", pos: string }
  | { kind: "ConstEvalCounter", pos: string }
  | { kind: "Intrinsic", intrinsic_kind: "Assume", operand: Operand, pos: string }
  | { kind: "Intrinsic", intrinsic_kind: "CopyNonOverlapping", src: Operand, dst: Operand, count: Operand, pos: string }

type Terminator =
    { kind: "Goto", target: BasicBlockInfo, pos: string }
  | { kind: "SwitchInt", discr: Operand, switch_ty: Ty, values: string?[], targets: BasicBlockInfo[], pos: string }
  | { kind: "Resume" | "Abort" | "Return" | "Unreachable" | "InlineAsm", pos: string }
  | { kind: "Drop", location: Lvalue, target: BasicBlockInfo, drop_fn: string?, pos: string }
  | { kind: "Call", func: Operand, args: Operand[], destination: [Lvalue,BasicBlockInfo]?, pos: string }
  | { kind: "Assert", cond: Operand, expected: boolean, msg: string, target: BasicBlockInfo, pos: string }



