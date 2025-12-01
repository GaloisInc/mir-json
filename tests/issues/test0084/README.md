# Test 0084: cargo saw-build/saw-rustc: Don't generate crux-mir-related test script

This test corresponds to [mir-json issue #84](https://github.com/GaloisInc/mir-json/issues/84).
It verifies that SAW builds (using `saw-rustc` or `cargo-saw-build`) do not
generate executable test scripts that invoke `crux-mir`, while Crux builds
(using `crux-rustc` or `cargo-crux-test`) do generate such scripts.

## Expected Behavior

- Pre-fix: SAW builds (using `saw-rustc` or `cargo-saw-build`) should create an
  executable "test" script that invokes crux-mir.
- Post-fix: no such script gets created.
