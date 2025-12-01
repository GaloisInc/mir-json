The following document describes the changes to the JSON schema that
`mir-json`–produced files adhere to. (This document should not be interpreted
as a changelog for the code in the `mir-json` tools themselves, which are
versioned separately.)

## 6

Upgrade the supported Rust toolchain to `nightly-2025-09-14` (`1.91`).

## 5

* Add a `needs_drop` field to interned types, tracking whether or not the type
  in question requires drop glue.

* Instantiations of const generic parameters are now represented with a
  `"kind": "Const"` object, where the object's `"constant"` key maps to the
  corresponding constant's rendered value. For instance, if a function `fn
  foo<const N: usize>()` were instantiated with `foo::<42>()`, then the
  instantiating type would be represented in the `tys` table and look something
  like this:

  ```json
  {
      "layout": null,
      "name": "ty::Const::abcd1234",
      "ty": {
          "kind": "Const",
          "constant": {
              "kind": "usize",
              "size": 8,
              "val": 42
          }
      }
  }
  ```

  Note that this convention does not apply to the sizes of array types, nor
  does it apply to value-level constants.

## 4

Add a field `tests`, subset of `roots`, which rememebers which of the
roots were marked as tests.

## 3

Emit layout information (size and alignment) for sized types.

## 2

Upgrade the supported Rust toolchain to `nightly-2025-02-16` (`1.86`).

## 1

Initial schema version, as of 20240910.

## Unversioned files prior to version 1

The schema used between 20240823 and 20240910 is the same as version
1, except without the version tag. Output from before this point is
different in various ways and no longer supported. In general any
unversioned files one may encounter should be recompiled; however,
any that came from a version of mir-json before 20240823 will not
be readable by downstream tools and must be rebuilt.
