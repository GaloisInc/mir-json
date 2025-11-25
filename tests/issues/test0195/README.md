A test which ensures that `mir-json` can successfully compile a test case that
`clone`s a function definition (in `rustc` parlance, a `TyKind::FnDef`) without
emitting a `don't know how to build clone shim for FnDef` warning, the subject
of [mir-json#195](https://github.com/GaloisInc/mir-json/issues/195).
