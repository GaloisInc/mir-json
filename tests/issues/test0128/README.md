# Test 0128: Projection Predicate Panic Reproducer

This test corresponds to [mir-json issue #131](https://github.com/GaloisInc/mir-json/issues/131), which documents the `ProjectionPredicate` panic.

This test script uses `saw-rustc` to compile the test case and confirms that the compilation does not trigger a panic inside the `mir-json` pipeline.

## Significance

This test ensures regression coverage for an issue where `mir-json` did not correctly handle `ProjectionPredicate` trait bounds within trait objects, causing a panic in `to_json.rs`.

## Expected Result

* Pre-`23a3006`: panic at `src/analyz/to_json.rs:140`
* Post-`23a3006`: no panic; MIR is successfully generated for `f` and associated trait definitions

