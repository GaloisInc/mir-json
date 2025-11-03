import { Ty, DefId, FnSig } from "common"
import { Fn } from "function"
import { Adt } from "adt"
import { ConstVal } from "constant"
import { Instance } from "instance"
import { NamedTy } from "type_table"

type MIR = {
  version: 4,
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

type Static = {
  kind: "constant" | "body",
  name: DefId,
  ty: Ty,
  mutable: boolean,
  rendered?: ConstVal
}



type Trait = {
  name: DefId,
  items: TraitItem[]
}

type TraitItem = {
  kind: "Method",
  item_id: DefId,
  signature: FnSig
}

type Vtable = {
  name : DefId,
  items: VtableItem[],
  trait_id: DefId
}

type VtableItem = {
  def_id: DefId,
  item_id: DefId
}

type Intrinsic = {
  name: DefId,
  inst: Instance
}

type LangItem = {
  orig_def_id: DefId,
  name: DefId
}
        