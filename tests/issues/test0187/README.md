A test which ensures that `mir-json` can successfully compile a test case
involving an `async` closure, the subject of [issue
#187](https://github.com/GaloisInc/mir-json/issues/187).

The body of an `async` closure gives rise to a _synthetic_ (i.e.,
compiler-generated) definitions at the MIR level, and at least as of
`nightly-2025-02-16`, attempting to query the attributes of this synthetic
closure body causes a panic. As such, `mir-json` has a special case for
synthetic definitions to avoid triggering this panic, and this test case
exercises that special case.
