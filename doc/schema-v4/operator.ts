type NullOp = {
  kind: "SizeOf" | "AlignOf" | "UbChecks"
}

type UnOp = {
  kind: "Not" | "Neg" | "PtrMetadata"
}

type BinOp = {
  kind:
    "Add" | "AddUnchecked" | "AddWithOverflow" |
    "Sub" | "SubUnchecked" | "SubWithOverflow" |
    "Mul" | "MulUnchecked" | "MulWithOverflow" |
    "Div" | "Rem" |
    "BitXor" | "BitAnd" | "BitOr" |
    "Shl" | "ShlUnchecked" | "Shr" | "ShrUnchecked" |
    "Eq" | "Lt" | "Le" | "Ne" | "Ge" | "Gt" |
    "Offset" | "Cmp"
}