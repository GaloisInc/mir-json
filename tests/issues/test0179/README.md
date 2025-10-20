A test which ensures that `mir-json` can successfully compile a test case that
creates a MIR constant whose type is an uninhabited enum, the subject of [issue
#179](https://github.com/GaloisInc/mir-json/issues/179).

Although one cannot create a value of an uninhabited enum type (e.g., `enum
Void {}`) in source Rust, `rustc` _can_ create constants of these types when
compiling to MIR. As such, `mir-json` has to be able to reckon with them. This
test case is one such example of a program where this happens. `mir-json` deals
with it by compiling the constant of type `Void` to a zero-sized type (`zst`)
value, similarly to how the never type (`!`) is handled.
