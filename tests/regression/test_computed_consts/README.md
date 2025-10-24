A test which checks that `mir-json` can successfully serialize instantiations
of const generic parameters involving non-trivial constants that involve some
amount of computation. This validates an assumption that `mir-json` makes
internally where it assumes that all type-level constants that it encounters
will reduce to
[`ConstKind::Value`](https://doc.rust-lang.org/1.86.0/nightly-rustc/rustc_middle/ty/type.ConstKind.html#variant.Value)
and not something else (e.g.,
[`ConstKind::Unevaluated`](https://doc.rust-lang.org/1.86.0/nightly-rustc/rustc_middle/ty/type.ConstKind.html#variant.Unevaluated)).
