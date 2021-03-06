# `rustc` integration in `crux-mir`

`mir-json` (the component of `crux-mir` responsible for interfacing with
`cargo` and `rustc`) consists of two main binaries:

* `cargo-crux-test`, a `cargo` subcommand, is the main user-facing entry point
  for `crux-mir`.
* `mir-json-rustc-wrapper`, a `RUSTC_WRAPPER` binary, uses `rustc_interface` to
  invoke normal `rustc` compilation with some additional callbacks installed.

In general, `crux-mir` tries to reuse as much of the normal `cargo`
functionality as possible.  `cargo-crux-test` makes some minor adjustments to
the command line arguments, sets up some environment variables (notably
`RUSTC_WRAPPER`), and then dispatches to `cargo test` to build and run the
symbolic tests.  Since `cargo-crux-test` is essentially just `cargo test` with
a special `RUSTC_WRAPPER`, it supports almost all the standard `cargo`
features, such as `build.rs` files, dependencies on proc-macro crates, and test
filtering flags like `--lib`/`--bin`.

`mir-json-rustc-wrapper` has three modes of operation:

1. If it detects that it's being invoked to build a `cargo` "host" dependency,
   such as a `build.rs` file or a proc-macro crate, it passes through all its
   arguments to ordinary `rustc` and performs no special behavior.  This is
   necessary because `mir-json` cannot produce working binaries or proc-macro
   crates; `crux-mir`'s custom `libstd` relies on verifier builtins, which
   would simply panic when compiled normally.

2. If it detects that it's being invoked to build a `cargo` "target"
   dependency, it invokes `rustc` with modified command-line arguments and
   additional callbacks.  `rustc` builds the crate as usual, except that (a)
   `libstd` and other sysroot libraries are replaced with the custom versions
   shipped with `crux-mir`, and (b) the callbacks emit a representation of the
   crate into a `.mir` file alongside the normal `.rlib` or other output.

3. Finally, if it is invoked with the `--test` flag, it behaves as in (2), with
   some additional changes to the command-line arguments.  Then, after
   building, it links together the `.mir` files for the crate being tested and
   all its dependencies, and replaces the test binary output with a script that
   invokes `crux-mir`'s symbolic execution backend on the linked `.mir`.


## `TyCtxt` usage

After obtaining the `TyCtxt` for the crate being compiled, `mir-json` uses it
in the following ways:

* Retrieving definitions: function/const/static signatures and bodies
  (`optimized_mir`, `type_of`, `fn_sig`); type definitions (`AdtDef`s obtained
  from `TyKind::Adt`); trait and trait impl methods (`vtable_methods`).

* Monomorphization: `mir-json` monomorphizes all the definitions it outputs.
  This applies not only to functions but also to structs and traits.  For
  example, in the output of `mir-json`, the types `Vec<bool>` and `Vec<i32>` are
  treated as two unrelated struct types, and `Iterator<Item = bool>` and
  `Iterator<Item = i32>` are two unrelated traits.  This involves the `TyCtxt`
  methods `subst_and_normalize_erasing_regions` and `instance_mir`, as well as
  `Instance::resolve` for resolving the target of a function call.

* Const evaluation: `mir-json` evaluates array lengths (after monomorphization)
  so it can output a literal `usize`.  It also uses a variety of functionality
  from `rustc_mir::interpret` module to process evaluated constants back into a
  form suitable for `crux-mir`'s more abstract memory model.  For example, the
  constant `None::<bool>` sometimes appears in the form `Scalar(0x02)`, which
  is its concrete representation as a byte; `mir-json` extracts the variant and
  field information (in this case, `Option::None` with no fields), which is the
  representation required by the `crux-mir` backend.

* Miscellaneous: `has_attr` for identifying symbolic tests (marked with the
  `#[crux_test]` attribute); `all_crate_nums` and related queries to identify
  dependencies; `output_filenames` to get the path of the normal `rustc` output
  (`mir-json` stores the `.mir` files it generates alongside the normal `.rlib`
  library output).
