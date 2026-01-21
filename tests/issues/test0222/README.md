A regression test for [issue
#222](https://github.com/GaloisInc/mir-json/issues/222). This ensures that
`mir-json` properly instantiates polymorphic `async` functions and normalizes
away any associated types that are captured by `async` closures.

This test was minimized from [this
example](https://github.com/tokio-rs/tokio/blob/8fd44d9bdc5af48c6d76aa4f3fddd45c18d0da43/examples/chat.rs)
from the `tokio` repository, which is under the MIT license.
