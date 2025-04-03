# Details of `translate_libs.sh`/`mir-json-translate-libs`

See [rustc.md](../rustc.md#translating-the-rust-standard-libraries) for basic
usage of `translate_libs.sh`.

`translate_libs.sh` is a thin wrapper around the `mir-json-translate-libs`
binary.

## `--generate`

If the `--generate` flag is passed to
`translate_libs.sh`/`mir-json-translate-libs`, it will not run `mir-json` or
permanently create any new files or directories. Instead, it will output to
stdout a series of shell commands which, when run, would do the same thing as
what it would have done directly. This is useful for debugging or if you just
want to see what `mir-json` commands would be run without actually running them.
The output can be directly saved into a shell script and executed at a later
point. Note that there will still be non-shell-script output on stderr.

Even with `--generate`, `mir-json-translate-libs` **will still run various
`cargo` commands, including builds**, and temporarily create files, in order to
determine which `mir-json` commands it should generate.

## Implementation

The dependencies of the standard libraries, and the compiler flags required to
build them, vary depending on the target and Rust version. Usually `cargo` uses
prebuilt versions of the standard libraries when building a project, but with
the `rust-src` rustup component installed, a nightly `cargo`, and the [`-Z
build-std`
flag](https://doc.rust-lang.org/cargo/reference/unstable.html#build-std) to
`cargo`, you can build the standard libraries locally. We want to build the
standard libraries in exactly the same way as `cargo test -Z build-std` does,
but with three changes:

1. Use `mir-json` instead of `rustc` as the compiler.
2. Use our patched versions of the standard libraries and their dependencies,
   instead of the ones in `rust-src` or on crates.io.
3. Add additional libraries needed by Crucible, possibly depending on, and/or as
   a dependency of, existing standard libraries.

Nightly `cargo` also has the [`--unit-graph`
option](https://doc.rust-lang.org/cargo/reference/unstable.html#unit-graph),
which outputs the dependency graph of the crates that it will build, including
the standard libraries if `-Z build-std` is also passed. So we essentially
create a new cargo project with `cargo init`, which will contain a simple binary
with no dependencies other than the standard libraries, and do `cargo test -Z
build-std --unit-graph` on that project to get the dependency graph of the
standard library crates, then modify the source file paths in the graph to point
to our patched versions, and add our additional libraries into the dependency
graph, before performing a topological sort and generating `mir-json` commands
for each unit in the graph.

However, many standard library crates actually have build scripts, which must be
run on the host to determine the exact configuration required to build the
actual library. `cargo test --unit-graph` does not run any builds, not even
build scripts, so its output is incomplete compared to what is actually passed
to `rustc` in a real `cargo test`. Therefore, we also run a real `cargo test -Z
build-std` on the new project, and capture `cargo`'s [JSON output
messages](https://doc.rust-lang.org/cargo/reference/external-tools.html#json-messages).
Unfortunately, `cargo` does not output the exact `rustc` invocations when asked
for JSON messages, but the `compiler-artifact` and `build-script-executed`
messages (in conjunction with the `--unit-graph` output) contain enough
information to piece together what we need to build a `mir-json` invocation, at
least for the purposes of building the standard libraries, so we add that
information to the unit graph to generate the final `mir-json` commands.
