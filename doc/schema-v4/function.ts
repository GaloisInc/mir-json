import { Abi, Ty, Var } from "common"
import { Lvalue, Rvalue, Operand } from "expr"

type Fn = {
  abi: Abi,
  name: string,
  args: Var[],
  body: MirBody,
  spread_arg: number?,
  return_ty: Ty
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

