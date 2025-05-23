# `rustc` integration in `crux-mir`

`mir-json` (the component of `crux-mir` responsible for interfacing with
`cargo` and `rustc`) consists of three main binaries:

* `cargo-crux-test`, a `cargo` subcommand, is the main user-facing entry point
  for `crux-mir`.
* `cargo-saw-build`, a `cargo` subcommand, is the main user-facing entry point
  for SAW's MIR verification support.
* `mir-json-rustc-wrapper`, a `RUSTC_WRAPPER` binary, uses `rustc_interface` to
  invoke normal `rustc` compilation with some additional callbacks installed.

These tools require a version of the Rust standard library that has been
translated with `mir-json`. The `CRUX_RUST_LIBRARY_PATH` or
`SAW_RUST_LIBRARY_PATH` environment variable should be defined with this path
before using one of these tools. Note that these two environment variables are
functionally equivalent, and the only difference is to more clearly signal
which tool is intended to be used in combination with `mir-json`.

## `cargo-crux-test`

In general, `crux-mir` tries to reuse as much of the normal `cargo`
functionality as possible.  `cargo-crux-test` makes some minor adjustments to
the command line arguments, sets up some environment variables (notably
`RUSTC_WRAPPER`), and then dispatches to `cargo test` to build and run the
symbolic tests.  Since `cargo-crux-test` is essentially just `cargo test` with
a special `RUSTC_WRAPPER`, it supports almost all the standard `cargo`
features, such as `build.rs` files, dependencies on proc-macro crates, and test
filtering flags like `--lib`/`--bin`.

## `cargo-saw-build`

`cargo-saw-build` is very similar in operation to `cargo-crux-test` in that
both will compile Rust code into a MIR JSON file. There are two primary
differences between `cargo-saw-build` and `cargo-crux-test`:

* `cargo-saw-build` will stop after producing the JSON file, whereas
  `cargo-crux-test` will proceed to run `crux-mir` on the JSON afterwards. The
  former is more useful for SAW's needs.

* `cargo-crux-test` expects users to annotate each function that they want to
  test with a `#[crux::test]` attribute (see the `mir-json-rustc-wrapper`
  section of this document). `cargo-saw-build`, on the other hand, assumes that
  all monomorphic, top-level functions should be reachable for SAW verification
  purposes. The operative word here is "monomorphic". If you have this program:

  ```rs
  pub fn id<A>(x: A) -> A {
      x
  }

  pub fn id_u32(x: u32) -> u32 {
      id(x)
  }
  ```

  Then SAW will be able to verify `id_u32` (which is monomorphic) but _not_ `id`
  (which is polymorphic).

## `mir-json-rustc-wrapper`

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

`mir-json-rustc-wrapper`'s behavior is controlled by a variety of environment
variables. Aside from `CRUX_RUST_LIBRARY_PATH`, it also uses the following
internal environment variables, which most users will not need to care about:

* `CRUX_MIR_ALREADY_SET_PATH`: If this environment variable is set, then the
  parent process has already set up the `LD_LIBRARY_PATH`/`DYLD_LIBRARY_PATH` to
  point to the appropriate `lib` directory for the Rust toolchain currently in
  use.
* `CRUX_USE_OVERRIDE_CRATES`: The list of crates for which `crucible-mir`
  overrides should be used.
* `EXPORT_ALL`: If this environment variable is set, then the MIR JSON file
  will export all top-level functions. Otherwise, it will only export those
  functions with a `#[crux::test]` attribute.

For the purposes of debugging `mir-json` itself, the environment variable
`MIR_JSON_USE_RUSTC_LIBRARY` can be defined (with any value) instead of
`CRUX_RUST_LIBRARY_PATH` or `SAW_RUST_LIBRARY_PATH`, in which case
`mir-json-rustc-wrapper` will use the vanilla standard library that comes with
`rustc` instead of a modified version for the compilation process. Since the
unmodified version is not supported by Crucible, the resulting JSON output
**will not work** with SAW or Crux when `MIR_JSON_USE_RUSTC_LIBRARY` is set.

## Other binaries

Besides the main binaries above, `mir-json` also provides a variety of other
binaries for specialized purposes.

### `cargo` subcommands

* `cargo-mir-json`: This invokes `cargo rustc`, but replacing `rustc` with
  `mir-json`.

### `rustc` replacements

* `crux-rustc`: A helper that invokes `mir-json-rustc-wrapper` the same way that
  `cargo-crux-test` would run it. This is useful for testing a single file,
  e.g., `crux-rustc --test foo.rs`.
* `saw-rustc`: A helper that invokes `mir-json-rustc-wrapper` the same way that
  `cargo-saw-build` would run it. This is useful for building a single file,
  e.g., `saw-rustc foo.rs`.

It is recommended that you invoke `{crux,saw}-rustc` with `--edition 2021` or
later. Invoking them with `--edition 2015` in particular has been observed to
produce undesirably large MIR JSON files (see [this
issue](https://github.com/GaloisInc/mir-json/issues/94) for more details).

### `mir-json` utilities

* `mir-json-callgraph`: This prints the reverse callgraph of a function, which
  can be helpful for debugging.
* `mir-json-dce`: This takes in several `.mir` files, combines them, and then
  runs dead-code elimination on them. It is unlikely that you will need to use
  this binary directly, as dead-code elimination is performed as an intermediate
  step in other binaries.
* `mir-json-translate-libs`: This calls `mir-json` to generate `.mir` files for
  our modified versions of the Rust standard libraries.
* `mir-json`: This produces a `.mir` file from a single `.rs` file and does not
  do anything else, such as testing with `crux-mir`. It is unlikely that you
  will need to use this binary directly, as producing `.mir` files is performed
  as an intermediate step in other binaries.

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
  `#[crux::test]` attribute); `all_crate_nums` and related queries to identify
  dependencies; `output_filenames` to get the path of the normal `rustc` output
  (`mir-json` stores the `.mir` files it generates alongside the normal `.rlib`
  library output).

# Translating the Rust standard libraries

`mir-json` requires slightly modified versions of the Rust standard libraries
that are simpler to formally reason about. These modified standard libraries are
located under the `libs/` subdirectory. After installing `mir-json`, you can run
the `mir-json-translate-libs` program to compile the standard libraries using
`mir-json`. It will create a directory called `rlibs_real` with a Rust sysroot
structure and a symlink `rlibs` into the subdirectory of `rlibs_real` which
contains the build artifacts. The path to `rlibs` can then be used as the value
of `CRUX_RUST_LIBRARY_PATH` or `SAW_RUST_LIBRARY_PATH`.

`mir-json-translate-libs` can take some optional command line arguments:

```
mir-json-translate-libs
Build the custom Rust standard libraries for mir-json

USAGE:
    mir-json-translate-libs [OPTIONS] [libs]

ARGS:
    <libs>    Directory containing custom Rust standard libraries [default: ./libs]

OPTIONS:
        --copy-sources <NEW_LIBS>    Instead of translating the existing custom standard libraries,
                                     copy all upstream standard library sources to NEW_LIBS (if they
                                     don't already exist there) and exit (used for upgrading Rust
                                     toolchain)
        --debug                      Emit debug output on stderr
        --generate                   Print a shell script instead of actually running the build
    -h, --help                       Print help information
        --keep-temp-build            Persist the temporary cargo package created to run `cargo test
                                     -Z build-std` to out-dir
    -o, --out-dir <OUT_DIR>          Directory to place rlibs and rlibs_real in [default: next to
                                     libs]
        --target <TARGET>            Rust target triple to configure the libraries for [default:
                                     host triple]
```

## `--target`

By default, `mir-json-translate-libs` compiles the libraries for your host
machine's architecture. If you want to cross-compile for a different target, you
can optionally pass a [target
triple](https://doc.rust-lang.org/nightly/rustc/platform-support.html) when
running `mir-json-translate-libs`. This is experimental and we have only tested
`wasm32-unknown-unknown` to work; you might get build errors for other targets.

## `--generate`

If the `--generate` flag is passed to `mir-json-translate-libs`, it will not run
`mir-json` or permanently create any new files or directories. Instead, it will
output to stdout a series of shell commands which, when run, would do the same
thing as what it would have done directly. This is useful for debugging or if
you just want to see what `mir-json` commands would be run without actually
running them. The output can be directly saved into a shell script and executed
at a later point. Note that there will still be non-shell-script output on
stderr.

Even with `--generate`, `mir-json-translate-libs` **will still run various
`cargo` commands, including builds**, and temporarily create files, in order to
determine which `mir-json` commands it should generate.
