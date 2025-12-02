A regression test for
[mir-json#201](https://github.com/GaloisInc/mir-json/issues/201). This ensures
that the output of "`rustc`-like" commands (i.e., `mir-json`,
`mir-json-rustc-wrapper`, `crux-rustc`, and `saw-rustc`) all print out the
`rustc` version information first (before `mir-json`-specific version
information) when passed the `--version` flag. This property is essential in
order to support building crates like `libc`, whose custom build script parses
`rustc --version` output. When building such crates with `mir-json` (where we
override `rustc` with a `mir-json`-specific wrapper binary), it is important to
mimic the `rustc --version` output just enough to make these custom build
scripts work.

This test performs a very basic smoke test to ensure that each of these
binaries print out "`rustc 1`" in their first line of standard output. This is
a decent-enough approximation of what `libc`'s build script checks for
([here](https://github.com/rust-lang/libc/blob/46845987076649c0458810e323162d5c8b40b61e/build.rs#L224-L228)).
