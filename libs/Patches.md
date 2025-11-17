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

  These require the `compare_bytes` intrinsic, which Crucible doesn't currently
  support. These also require pointer casts to `*const u8` that Crucible can't
  support.

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

* Don't deallocate in `Box::drop` (last applied: April 24, 2025)

  Crucible doesn't support a `deallocate` operation.

* Don't deallocate in `Arc::drop` and related functions (last applied: April 25, 2025)

  Crucible doesn't support a `deallocate` operation.

* Skip `addr_eq` debug asserts in `Arc::drop` (last applied: April 25, 2025)

  `Arc::drop` (and its corresponding `Weak::drop`) has a `debug_assert!` to
  guard against attempts to drop the statically-allocated `Arc` used for
  `Arc::<[T]>::default()`.  This check calls `ptr::addr_eq`, which is
  unsupported by crucible-mir (though it probably wouldn't be too hard to add).

* Always use `crucible::TypedAllocator` in `RawVecInner` (last applied: April 28, 2025)

  Upstream has polymorphized the `RawVec` implementation by factoring out most
  of the logic into a new `RawVecInner` type that's parameterized only by an
  allocator, not by the element type `T`.  This makes it difficult to switch
  over to crucible-mir's allocation functions, which require the element type.
  This patch modifies `RawVec` to always instantiate `RawVecInner` with
  `crucible::TypedAllocator<T>` as its allocator, which is minimally invasive
  and has the effect of threading the element type through to the crucible-mir
  allocation functions.

* Use `Box::new` instead of `box_new` in `vec!` macro (last applied: April 28, 2025)

  Calls to the intrinsic `alloc::boxed::box_new` get compiled down to calls to
  `exchange_malloc`, which is an untyped allocation function and thus
  unsupported by crucible-mir.

* Remove calls to `three_way_compare` intrinsic (last applied: April 28, 2025)

  The `PartialOrd` and `Ord` impls for integers are implemented with the
  `three_way_compare` intrinsic, which compiles down to `BinOp::Cmp`.  This
  operation is not supported in crucible-mir, so this patch replaces the
  intrinsic calls with some ordinary two-way comparisons.

* Replace end pointer with length in slice iterator (last applied: April 28, 2025)

  The standard library implementation of slice iterators for non-ZSTs consists
  of a start pointer and an end pointer.  This is a problem because pointer
  equality may fail in crucible-mir if the pointers use `Const_RefRoot`.  For
  ZSTs, the implementation casts the length to a pointer and stores it in place
  of the end pointer.  This is a problem because crucible-mir doesn't support
  pointer-to-integer casts, which are used when updating the length.  This
  patch fixes both issues by changing the representation to consist of a start
  pointer and an integer length, for both ZST and non-ZST cases.

  We may be able to get rid of this patch in the future.  For the non-ZST case,
  the issue only occurs with `Const_RefRoot`, which is rarely used; we could
  remove the last use of it in `Override.hs`, maybe by generating a fresh
  Crucible `RefCell` instead.  For the ZST case, we could add support for
  casting `MirReference_Integer` pointers back to an integer, which would allow
  for the `pointer -> integer -> pointer` casts that are used in the iterator.

* Implement `HashMap` in terms of `Vec` (last applied: May 1, 2025)

  The actual implementation (in terms of `hashbrown`) is too complicated for
  Crucible to handle effectively. In particular, it has a mixed-type allocation
  that we don't support. It makes one big allocation and uses the first N bytes
  as flags and the remaining M bytes as key-value pairs.

* Don't check for overlapping references in `Cell::swap` (last applied: May 6, 2025)

  The actual implementation of `cell::swap` checks for overlapping `Cell`
  references before performing the swap and panics if there is overlap. The
  overlap check relies pointer-to-integer casts that `crucible-mir` does not
  currently support. As such, we omit the check. This is fine for now, since
  the only way to get overlapping `Cell` references is by producing `&Cell<T>`
  values, but `crucible-mir` does not currently support the operations for
  producing `&Cell<T>` values (see [this
  commit](https://github.com/GaloisInc/crucible/commit/e703d3014c50a999d3913460dcd99d17ab4f1e9f)).

* Use `no_threads` version of `condvar`, `mutex`, and `rwlock` (last applied: May 6, 2025)

  Because Crucible is effectively single-threaded, we can use `std`'s
  `no_threads` implementations of locks which are much simpler than the real
  ones. Also, we add calls to crucible intrinsics for mutex lock and unlock for
  concurrent crucible support.

* Replace `sys::time` with Crux-specific implementation (last applied: May 8, 2025)

  Crux's version is not suitable for doing actual timing (it hard-codes the
  time to a fixed date), but it does simulate much more easily than the actual
  implementation.

* Remove `*T` to `*[T; N]` cast in `[T; N]::try_from(Vec<T, A>)` (last applied: May 23, 2025)

  Crucible does not currently support pointer casts from single elements to
  arrays, so we implement this function by explicitly creating a
  `MaybeUninit<[T; N]>` and copying into it.

* Avoid use of `const { MaybeUninit::uninit() }` (last applied: October 10, 2025)

  Crucible doesn't support `MaybeUninit::uninit()` in const contexts.  In
  general, producing rendered constants for unions (like `MaybeUninit`) is
  difficult because we don't have a good way to detect which union variant is
  active.

* Use `crucible_array_from_ref_hook` in `core::array::from_ref` (last applied: July 22, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle.

* Replace `NonNull::cast` with `transmute` in `TypedAllocator` allocation (last applied: July 25, 2025)

  Its use of `cast`, specifically for `NonNull<[u8; N]>` pointers, can conflict
  with Crucible's representation of arrays.

* Use `crucible_slice_from_mut_hook` in `core::slice::from_mut` (last applied: July 25, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle.

* Use `crucible_slice_from_ref_hook` in `core::slice::from_ref` (last applied: July 28, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle.

* Replace `{*mut,NonNull}::cast` with `transmute` in `RawVec` initialization (last applied: July 28, 2025)

  Its use of `cast`, specifically for `NonNull<[u8; N]>` pointers, can conflict
  with Crucible's representation of arrays.

* Simplify optimized implementation of `fmt_u128` (last applied: August 28, 2025)

  The `Display` impls for `u128` and `i128` are defined in terms of a heavily
  optimized `fmt_u128` function that is difficult for `crucible-mir` to
  translate. (Among other things, it performs `f64`-to-`u64` conversions and
  calls the `write_bytes` intrinsic, neither of which are currently supported.)
  We replace this function with a slower (but easier-to-translate),
  macro-generated version.
