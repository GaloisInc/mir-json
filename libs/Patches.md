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

* Remove the most common uses of `ptr::from_raw_parts` (last applied: April 22, 2025)

  The `ptr::from_raw_parts` function implicitly performs a pointer cast through
  the `AggregateKind::RawPtr` intrinsic, which is difficult for crucible-mir to
  support due to [crucible#1385](https://github.com/GaloisInc/crucible/issues/1385).
  This patch removes direct calls to `ptr::from_raw_parts` from `ptr::null`,
  `ptr::slice_from_raw_parts`, and `slice::from_raw_parts`, and removes an
  indirect use through `byte_add` from `Option::as_slice`.

* Use `crucible_array_from_slice_hook` in `<[T]>::as_slice` (last applied: April 22, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle.

* Avoid `transmute` in `Layout` and `Alignment` (last applied: April 22, 2025)

  `Alignment::new_unchecked` uses `transmute` to convert an integer to an enum
  value, assuming that the integer is a valid discriminant for the enum.
  `Layout::from_size_align` performs the same `transmute` operation directly,
  bypassing `Alignment::new_unchecked`.  This patch reimplements
  `Alignment::new_unchecked` without `transmute` and modifies `Layout` to call
  it.  Finally, this patch removes a `transmute` in the opposite direction from
  `Alignment::as_usize`.

* Add a hook in `NonZero::new` (last applied: April 22, 2025)

  The new generic `NonZero::new` relies on transmute to convert `u32` to
  `Option<NonZero<u32>>` in a const context.  Removing this transmute is
  difficult due to limited ability to use generics in a const context.
  Instead, we wrap it in a hook that we can override in crucible-mir.

* Use crucible's allocator in `Box` constructors (last applied: April 24, 2025)

  Rust's allocator API returns untyped memory, similar to `malloc`, and `Box`
  casts the result from `*mut u8` to `*mut T`.  Since crucible-mir works only
  with typed memory, we replace the allocator calls in `Box::new` and related
  functions to call built-in Crucible allocation functions instead (e.g.
  `crucible::alloc::allocate`).
