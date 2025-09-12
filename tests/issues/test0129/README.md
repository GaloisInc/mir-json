# Test 0129: Nested Static Panic Reproducer

This test corresponds to [mir-json issue #129](https://github.com/GaloisInc/mir-json/issues/129), which documents an internal error when compiling code with nested static items.

This test script uses `saw-rustc` to compile the test case and confirms that the compilation does not trigger an internal panic or error inside the `mir-json` pipeline.

## Expected Result

* Pre-fix: panic or internal error (typically from `rustc_middle/src/hir/map/mod.rs:952:32`).
* Post-fix: no panic; MIR is successfully generated for `f` and associated static definitions.
