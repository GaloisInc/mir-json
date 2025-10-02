A test which checks that `mir-json` can successfully link together two
different crates that share the same constants (`42u8` and `42usize`). This
also ensures that there aren't any issues with the same constant-related
mangled names being defined in two different places.
