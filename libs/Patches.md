# Patching the Rust standard library

This directory bundles a copy of the Rust standard library with various patches
applied in certain key places to make the resulting code easier for Crucible to
handle. These patches must be applied every time that the bundled Rust standard
library is updated. Moreover, this code often looks quite different each time
between Rust versions, so applying the patches is rarely as straightforward as
running `git apply`.

As a compromise, this document contains high-level descriptions of each type of
patch that we apply, along with the date in which it was last applied and the
rationale for why the patch is necessary. The intent is that this document can
be used in conjunction with `git blame` to identify all of the code that was
changed in each patch. If the rationale for a patch is particularly in-depth,
consider splitting it out into a section in the "Notes" section below.

If you need to update the implementation of a patch later, make sure to include
an *Update* line (along with a date) describing what the patch does. That way,
when the next Rust toolchain upgrade is performed, the update can be folded
into the main commit for that patch, and then the *Update* line can be removed.

* Add reference to `core::crucible` module (last applied: June 9, 2026)

  After adding the crucible intrinsics in `core/src/crucible`, we need to add a
  reference to it in `core/src/lib.rs`.

* Disable `BytewiseEq`-based array/slice comparisons (last applied: June 9, 2026)

  These require a special comparison intrinsic (`core::intrinsics::raw_eq`)
  that Crucible doesn't support. We instead fall back on the other
  `SpecArrayEq`/`SlicePartialEq` instances that are slower (but easier to
  translate).

* Avoid use of `const { MaybeUninit::uninit() }` (last applied: June 9, 2026)

  Crucible doesn't support `MaybeUninit::uninit()` in const contexts.  In
  general, producing rendered constants for unions (like `MaybeUninit`) is
  difficult because we don't have a good way to detect which union variant is
  active.  This specifically affects `array::from_fn` and
  `Iterator::next_chunk`.

* Use `crucible_array_from_ref_hook` in `core::array::from_ref` (last applied: June 9, 2026)

  The actual implementation uses a pointer cast that Crucible can't handle.
