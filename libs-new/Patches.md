# Patching the Rust standard library

This directory bundles a copy of the Rust standard library with various patches
applied in certain key places to make the resulting code easier for Crucible to
handle. These patches must be applied every time that the bundled Rust standard
library is updated. Moreover, this code often looks quite different each time
between Rust versions, so applying the patches is rarely as straightforward as
running `git apply`.

As a compromise, this document contains high-level descriptions of each type of
patch that we apply, along with rationale for why the patch is necessary. The
intent is that this document can be used in conjunction with `git blame` to
identify all of the code that was changed in each patch.

* Use `crucible::ptr::compare_usize` for pointer-integer comparisons (last applied: April 17, 2025)

  The `is_null` method on pointers works by casting the pointer to an integer
  and comparing to zero.  However, crucible-mir doesn't support casting valid
  pointers to integers (e.g. `&x as *const _ as usize` will always fail).  We
  reimplement `is_null` in terms of `crucible::ptr::compare_usize(ptr, n)`,
  which directly checks whether `ptr` is the result of casting `n` to a pointer
  type.

  The internal function `alloc::rc::is_dangling` is implemented similarly to
  `is_null`, so we reimplement it in terms of `compare_usize` as well.

* Disable `IsRawEqComparable`-based `SpecArrayEq` instances (last applied: April 18, 2025)

  These require pointer casts that Crucible can't support. We instead fall back
  on the other `SpecArrayEq` instances that are slower (but easier to
  translate).

* Disable bytewise equality comparisons for `[T]` (last applied: April 18, 2025)

  These require the `size_of_val` intrinsic, which isn't current supported.
