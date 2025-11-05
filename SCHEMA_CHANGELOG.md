The following document describes the changes to the JSON schema that
`mir-json`–produced files adhere to. (This document should not be interpreted
as a changelog for the code in the `mir-json` tools themselves, which are
versioned separately.)

## 5

Add a `needs_drop` field to interned types, tracking whether or not the type in
question requires drop glue.

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
