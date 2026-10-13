A regression test for [issue
#241](https://github.com/GaloisInc/mir-json/issues/241). This ensures that
`mir-json` can compile code that constant-evaluates something that uses a
reference with a non-zero offset. Currently, `mir-json` emits `"unsupported"`
for such constant references, so this test also checks for this property.
