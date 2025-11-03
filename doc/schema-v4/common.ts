type DefId = string

type Ty = string

type Var = {
  // Is this a zero size type?
  is_zst: boolean,
  mut: Mutability,
  name: string,
  ty: Ty
}

type Mutability = {
  kind: "MutMutable" | "Mut" | "MutImmutable" | "Not"
}

// Calling convention for this function
type Abi = {
  kind: string,
  ...
}

type FnSig = {
  inputs: Ty[],
  output: Ty,
  abi: Abi
}