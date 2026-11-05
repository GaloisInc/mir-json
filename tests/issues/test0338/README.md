A regression test for [issue
#338](https://github.com/GaloisInc/mir-json/issues/338). This ensures that
`mir-json` can compile `no_std` code using the `cryptol!` and
`crucible_assert!` macros in a way that requires string formatting.
