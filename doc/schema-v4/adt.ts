import { DefId, Ty } from "common"

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