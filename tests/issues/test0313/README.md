A regression test for [issue
#313](https://github.com/GaloisInc/mir-json/issues/313). This ensures that
`mir-json` can compile code that denies the use of unstable Rust features.
(Note that a previous version of `mir-json` would register the `crux` tool
using an unstable Rust feature, so this test ensures that the current mechanism
bypasses Rust's unstable feature check.)
