A test which ensures that `mir-json` can successfully compile a test case
involving a `CoroutineWitness` type, the subject of [mir-json issue
#166](https://github.com/GaloisInc/mir-json/issues/166) remains fixed.

`CoroutineWitness`es are quasi-types that are emitted when compiling the
"synthetic" parameters for coroutine-related closures, which means that
although they appear in the emitted MIR code, the closures aren't really
generic over `CoroutineWitness` types. This style of code is used by the
internals of Rust's `async` machinery, as commonly used in libraries like
`tokio`.

Do note that `CoroutineWitness` has been removed entirely in recent Rust
nightlies, and Rust's coroutine syntax itself is unstable. As such, this test
case may need to be updated in a future upgrade to ensure that we have _some_
amount of test coverage for `async`-related code. Just in case the
`#[coroutine]` syntax is removed entirely, I have also added another function
that uses an `async fn` instead of using `#[coroutine]`. The assumption is that
the former is likely to compile to the latter, but the former's syntax is
stable than the latter's.
