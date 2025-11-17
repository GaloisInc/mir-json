# Test 0050: saw-rustc Info Flags Crash

This test corresponds to [mir-json issue
#50](https://github.com/GaloisInc/mir-json/issues/50), which documents a crash
when running `saw-rustc` with informational flags like `--version` or `--help`.

## Expected Result

* Pre-fix: Panic at `mir-json-rustc-wrapper.rs` when using `saw-rustc` with info flags
* Post-fix: All info flags work correctly, printing the expected information without panicking
