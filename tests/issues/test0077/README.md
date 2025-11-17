# Test 0077: version printing

This test corresponds to [mir-json issue
#77](https://github.com/GaloisInc/mir-json/issues/77), a request for the
`mir-json` tools to print version info for `mir-json` and not just for `rustc`.
These tests verify `mir-json` and JSON schema version info strings get printed
for `mir-json` tools.

## Expected Result

* Pre-fix: only `rustc` version info printed for `--version` flag.
* Post-fix: `rustc` version info is preceded by "mir-json MIR_JSON_VERSION
  (JSON schema version SCHEMA_VERSION)".

