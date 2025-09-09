# Regression Test: Output Schema Check

This test verifies that the `mir-json` pipeline produces MIR JSON output containing an expected function, and that the output matches basic structural expectations.

## Purpose

- Confirms that `mir-json` runs successfully (no panic).
- Checks that the generated `test.linked-mir.json` file contains a function whose name ends with `::call_foo`.
- Demonstrates how jq-based checks can be used to verify structural properties of MIR JSON output, beyond simple panic/success tests.

## Files

- `test.rs` — Minimal Rust source defining a trait, an implementation, and a function (`call_foo`) using a trait object.
- `test.sh` — Test script: runs `saw-rustc`, then uses `jq` to check for the presence of `call_foo` in the output.

## Expected Result

- The test passes if `mir-json` completes without error and the output JSON contains a function named `*::call_foo`.
- The test fails if either a panic occurs or the expected function is missing from the output.

## Notes

- This test is not tied to any specific bug or issue, but acts as an exemplar regression check for the basic structure of MIR JSON output.
