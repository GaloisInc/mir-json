import { Ty, DefId } from "common"

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
  | { kind: "tuple", elements: ConstVal[] }
  | { kind: "closure", upvars: ConstVal[] }
  | { kind: "fn_ptr", "def_id": DefId }