A regression test for [issue
#210](https://github.com/GaloisInc/mir-json/issues/210). This ensures that
`mir-json` can compile code that constant-evaluates something that uses a
custom, dynamically sized type (DST). Currently, `mir-json` emits
`"unsupported"` for such DST constants, so this test also checks for this
property.
