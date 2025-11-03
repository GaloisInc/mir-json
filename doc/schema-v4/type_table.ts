import { Ty, DefId, Mutability, FnSig } from "common"
import { Constant } from "constant"

type NamedTy = {
  name:   string,
  ty:     InlineType,
  layout: Layout?
}

type InlineType =
    { kind: "Bool" | "Char" | "Str" | "Never" | "Foreign" }
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

type BaseSize = {
  kind: "Usize" | "U8" | "U16" | "U32" | "U64" | "U128" |
        "Isize" | "I8" | "I16" | "I32" | "I64" | "I128"
}
            
type FloatKind = { kind: "F32" | "F64" }

type Layout = {
  align: number,
  size: number
}

       