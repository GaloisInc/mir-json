A test which ensures that `mir-json` can successfully compile a test case that
`clone`s an array without warnings, the subject of
[mir-json#197](https://github.com/GaloisInc/mir-json/issues/197). This used to
require creating a `clone` shim, but as of
https://github.com/rust-lang/rust/pull/86041, `Clone` impls for array types are
now implemented in library code rather using `clone` shims. As such, `mir-json`
no longer needs any `clone` shim logic for arrays, and it should be able to
compile the given test case without issues.
