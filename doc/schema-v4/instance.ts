import { DefId, Ty } from "common"

type Instance =
   { kind: "Item" | "Intrinsic" | "VtableShim" | "ReifyShim", def_id: DefId, args: Ty[] }
 | { kind: "FnPtrShim", ty: Ty, def_id: DefId, args: Ty[] }
 | { kind: "Virtual", trait_id: DefId, index: number, item_id: DefId }
 | { kind: "ClosureOnceShim", call_once: DefId, args: Ty[] }
 | { kind: "DropGlue", ty: Ty?, def_id: DefId, args: Ty?[] }
 | { kind: "ClosureShim", ty: Ty, callees: DefId[], def_id: DefId, args: Ty[] }
 | { kind: "ClosureFnPointerShim", call_mut: DefId }