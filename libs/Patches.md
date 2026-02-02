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

* Add reference to `core::crucible` module (last applied: November 18, 2025)

  After adding the crucible intrinsics in `core/src/crucible`, we need to add a
  reference to it in `core/src/lib.rs`.

* Use `crucible::ptr::compare_usize` for pointer-integer comparisons (last applied: November 17, 2025)

  The `is_null` method on pointers works by casting the pointer to an integer
  and comparing to zero.  However, crucible-mir doesn't support casting valid
  pointers to integers (e.g. `&x as *const _ as usize` will always fail).  We
  reimplement `is_null` in terms of `crucible::ptr::compare_usize(ptr, n)`,
  which directly checks whether `ptr` is the result of casting `n` to a pointer
  type.

  The internal function `alloc::rc::is_dangling` is implemented similarly to
  `is_null`, so we reimplement it in terms of `compare_usize` as well.

* Disable `IsRawEqComparable`-based `SpecArrayEq` instances (last applied: November 17, 2025)

  These require pointer casts that Crucible can't support. We instead fall back
  on the other `SpecArrayEq` instances that are slower (but easier to
  translate).

* Disable bytewise equality comparisons for `[T]` (last applied: November 19, 2025)

  These require the `compare_bytes` intrinsic, which Crucible doesn't currently
  support. These also require pointer casts to `*const u8` that Crucible can't
  support.

* Remove the use of `ptr::from_raw_parts` from `ptr::null` (last applied: November 20, 2025)

  The `ptr::from_raw_parts` function implicitly performs a pointer cast through
  the `AggregateKind::RawPtr` intrinsic, which crucible-mir does not support for
  non-slice types. This patch removes direct calls to `ptr::from_raw_parts` from
  `ptr::null` and `ptr::null_mut`.

* Use `crucible_array_from_slice_hook` in `<[T]>::as_slice` (last applied: November 19, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle. See
  also the "Mark hook functions as `#[inline(never)]`" note below.

  *Update* (December 3, 2025): Add an `#[inline(never)]` attribute.

* Avoid `transmute` in `Layout` and `Alignment` (last applied: November 19, 2025)

  `Alignment::new_unchecked` uses `transmute` to convert an integer to an enum
  value, assuming that the integer is a valid discriminant for the enum.
  `Layout::from_size_align` performs the same `transmute` operation directly,
  bypassing `Alignment::new_unchecked`.  This patch reimplements
  `Alignment::new_unchecked` without `transmute` and modifies `Layout` to call
  it.  Finally, this patch removes a `transmute` in the opposite direction from
  `Alignment::as_usize`.

* Add a hook in `NonZero::new` (last applied: November 19, 2025)

  The new generic `NonZero::new` relies on transmute to convert `u32` to
  `Option<NonZero<u32>>` in a const context.  Removing this transmute is
  difficult due to limited ability to use generics in a const context. Instead,
  we wrap it in a hook that we can override in crucible-mir. See also the "Mark
  hook functions as `#[inline(never)]`" note below.

  *Update* (December 3, 2025): Add an `#[inline(never)]` attribute.

* Use crucible's allocator in `Box` constructors (last applied: November 17, 2025)

  Rust's allocator API returns untyped memory, similar to `malloc`, and `Box`
  casts the result from `*mut u8` to `*mut T`.  Since crucible-mir works only
  with typed memory, we replace the allocator calls in `Box::new` and related
  functions to call built-in Crucible allocation functions instead (e.g.
  `crucible::alloc::allocate`).

* Define `Arc`/`Rc` constructors in terms of `{Arc,Rc}::new` (last applied: January 20, 2026)

  This ensures that all `Arc`/`Rc` constructors are defined in terms of
  `Box::new`, which uses Crucible's typed allocator instead of Rust's untyped
  allocator. (See the `` Use crucible's allocator in `Box` constructors ``
  patch above.)

* Don't deallocate in `Box::drop` (last applied: November 17, 2025)

  Crucible doesn't support a `deallocate` operation.

* Don't deallocate in `Arc::drop`, `Rc::drop`, and related functions (last applied: November 17, 2025)

  Crucible doesn't support a `deallocate` operation.

  *Update* (January 20, 2026): Also patch out `Rc`-related functions (e.g.,
  `Rc::drop`).

* Skip `addr_eq` debug asserts in `Arc::drop` (last applied: November 20, 2025)

  `Arc::drop` (and its corresponding `Weak::drop`) has a `debug_assert!` to
  guard against attempts to drop the statically-allocated `Arc` used for
  `Arc::<[T]>::default()`.  This check calls `ptr::addr_eq`, which is
  unsupported by crucible-mir (though it probably wouldn't be too hard to add).

* Always use `crucible::TypedAllocator` in `RawVecInner` (last applied: November 19, 2025)

  Upstream has polymorphized the `RawVec` implementation by factoring out most
  of the logic into a new `RawVecInner` type that's parameterized only by an
  allocator, not by the element type `T`.  This makes it difficult to switch
  over to crucible-mir's allocation functions, which require the element type.
  This patch modifies `RawVec` to always instantiate `RawVecInner` with
  `crucible::TypedAllocator<T>` as its allocator, which is minimally invasive
  and has the effect of threading the element type through to the crucible-mir
  allocation functions.

* Use `Box::new` instead of `box_new` in `vec!` macro (last applied: November 20, 2025)

  Calls to the intrinsic `alloc::boxed::box_new` get compiled down to calls to
  `exchange_malloc`, which is an untyped allocation function and thus
  unsupported by crucible-mir.

* Remove calls to `three_way_compare` intrinsic (last applied: December 1, 2025)

  The `PartialOrd` and `Ord` impls for integers are implemented with the
  `three_way_compare` intrinsic, which compiles down to `BinOp::Cmp`.  This
  operation is not supported in crucible-mir, so this patch replaces the
  intrinsic calls with some ordinary two-way comparisons.

* Replace end pointer with length in slice iterator (last applied: December 1, 2025)

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

* Implement `HashMap` in terms of `Vec` (last applied: November 21, 2025)

  The actual implementation (in terms of `hashbrown`) is too complicated for
  Crucible to handle effectively. In particular, it has a mixed-type allocation
  that we don't support. It makes one big allocation and uses the first N bytes
  as flags and the remaining M bytes as key-value pairs.

* Use `crucible_cell_swap_is_nonoverlapping_hook` in `Cell::swap` (last applied: December 1, 2025)

  The actual implementation of `cell::swap` checks for overlapping `Cell`
  references before performing the swap and panics if there is overlap. The
  overlap check relies pointer-to-integer casts that `crucible-mir` does not
  currently support. As such, we use a Crucible override for the overlap check.
  See also the "Mark hook functions as `#[inline(never)]`" note below.

  *Update* (December 3, 2025): Add an `#[inline(never)]` attribute.

* Use `no_threads` version of `condvar`, `mutex`, and `rwlock` (last applied: November 27, 2025)

  Because Crucible is effectively single-threaded, we can use `std`'s
  `no_threads` implementations of locks which are much simpler than the real
  ones. Also, we add calls to crucible intrinsics for mutex lock and unlock for
  concurrent crucible support.

* Replace `sys::time` with Crux-specific implementation (last applied: November 25, 2025)

  Crux's version is not suitable for doing actual timing (it hard-codes the
  time to a fixed date), but it does simulate much more easily than the actual
  implementation.

* Always use regular `sleep` in `std::sys::thread::unix::sleep_until` (last applied: December 2, 2025)

  The `sleep_until` implementation on unix tries to use `clock_nanosleep` when
  applicable, by getting a `Timespec` out of the passed-in `time::Instant`. Our
  Crux-specific time implementation does not have a `Timespec` in it, so we
  instead always use the regular `sleep` function just like on other platforms.

* Remove `*T` to `*[T; N]` cast in `[T; N]::try_from(Vec<T, A>)` (last applied: December 1, 2025)

  Crucible does not currently support pointer casts from single elements to
  arrays, so we implement this function by explicitly creating a
  `MaybeUninit<[T; N]>` and copying into it.

* Avoid use of `const { MaybeUninit::uninit() }` (last applied: November 25, 2025)

  Crucible doesn't support `MaybeUninit::uninit()` in const contexts.  In
  general, producing rendered constants for unions (like `MaybeUninit`) is
  difficult because we don't have a good way to detect which union variant is
  active.

* Use `crucible_array_from_ref_hook` in `core::array::from_ref` (last applied: November 25, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle. See
  also the "Mark hook functions as `#[inline(never)]`" note below.

  *Update* (December 3, 2025): Add an `#[inline(never)]` attribute.

* Replace `NonNull::cast` with `transmute` in `TypedAllocator` allocation (last applied: July 25, 2025)

  Its use of `cast`, specifically for `NonNull<[u8; N]>` pointers, can conflict
  with Crucible's representation of arrays.

* Use `crucible_slice_from_mut_hook` in `core::slice::from_mut` (last applied: November 25, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle. See
  also the "Mark hook functions as `#[inline(never)]`" note below.

  *Update* (December 3, 2025): Add an `#[inline(never)]` attribute.

* Use `crucible_slice_from_ref_hook` in `core::slice::from_ref` (last applied: November 25, 2025)

  The actual implementation uses a pointer cast that Crucible can't handle. See
  also the "Mark hook functions as `#[inline(never)]`" note below.

  *Update* (December 3, 2025): Add an `#[inline(never)]` attribute.

* Replace `{*mut,NonNull}::cast` with `transmute` in `RawVec` initialization (last applied: November 27, 2025)

  Its use of `cast`, specifically for `NonNull<[u8; N]>` pointers, can conflict
  with Crucible's representation of arrays.

* Avoid `transmute` in `impl PartialEq for TypeId` (last applied: December 1, 2025)

  Crucible doesn't support transmuting a struct into a `u128`. We always use the
  `type_id_eq` fallback instead.

* Remove the dynamic CPU support detection in `memchr` package (last applied: November 24, 2025)

  This feature was using an `AtomicPtr<()>` with a cast from function
  pointer to `*mut ()` that we don't support in its initializer.

* Replace raw pointer cast in `std::hash` (last applied: January 22, 2026)

  Crucible doesn't currently support casting a `*mut u32` pointer to a `*mut
  u8` and then trying to write `u8` values into it. We instead rewrite the code
  slightly such that we build a `&mut [u8]` slice and then cast it to a `*mut
  u8`, thereby avoiding the need for `u32` altogether.

* Return dummy location in `Location::caller` (last applied: January 22, 2026)

  `crucible-mir` does not currently support the `intrinsics::caller_location()`
  intrinsic. To prevent this function from throwing translation errors, we have
  it return a constant dummy location.

* Avoid raw pointer comparisons in `std::thread` (last applied: January 22, 2026)

  `std::thread` reserves raw pointers with the addresses 0-2 as sentinel
  values. Instead of checking if a thread's pointer is not a sentinel value by
  seeing if it is larger than the sentinel with the largest address, we instead
  check if the pointer is not equal to each of the individual sentinel values.
  See also the "Avoid raw pointer comparisons" note below.

* Add `{Arc,Rc}::{from,inner}_into_raw` API functions (last applied: January 22, 2026)

  `crucible-mir` is not currently able to simulate the
  `{Arc,Rc}::{from,inner}_raw` functions, as they rely on non-trivial pointer
  offsets plus read from type-casted pointers.
  `{Arc,Rc}::{from,inner}_into_raw` offer alternatives with very similar types,
  but which are implemented in a Crucible-friendly way. We use these functions
  in the internals of `std::thread`.

  See also the "`{Arc,Rc}::{from,inner}_into_raw`" below.

# Notes

This section contains more detailed notes about why certain patches are written
the way they are. If you plan to reapply a patch that references one of these
notes, please make sure that the spirit of the note is still upheld in the new
patch. Alternatively, if you choose to deviate from the note, make sure to do
so after carefully considering why deviating is the right choice, and consider
updating the note in the process.

## Mark hook functions as `#[inline(never)]`

We want to ensure that custom hook functions (e.g.,
`crucible_array_from_slice_hook`) are always present in generated MIR code,
regardless of whether or not optimizations are applied. In some cases, it may
not suffice to compile the code containing the hook functions without
optimizations (as `mir-json-translate-libs` currently does), as `rustc` can
still inline code that is contained in a different compilation unit. (See
[#153](https://github.com/GaloisInc/mir-json/issues/153) for an example where
this actually happened.)

As a safeguard, we mark all custom hook functions as `#[inline(never)]` to
ensure that they persist when optimizations are applied.

## Avoid raw pointer comparisons

We avoid using `PartialOrd`-based comparisons with raw pointers values, e.g.,

```rs
fn f(p: *const ()) {
    if (p > ptr::null()) {
        ...
    }
}
```

Instead, we prefer using `PartialEq`-based equality checks, e.g.,

```rs
    if (p != ptr::null()) {
        ...
    }

```

The reason for this is because the `PartialOrd` impl for raw pointers compares
their underlying addresses, but `crucible-mir` pointers do not always have
addresses. `MirReference_Integer` pointers can treat their underlying integer
as an address (e.g., `ptr::null()` has the address 0), but other forms of
`MirReference`s (i.e., _valid_ `MirReference`s) do not have a tangible address,
so it is not currently possible to compare `MirReference_Integer`s against
valid `MirReference`s. Attempting to do so will raise a simulation error.

Using the `PartialEq` impl for raw pointers works better in a `crucible-mir`
context. Instead of raising a simulation error, `crucible-mir` will simply
return `False` when checking if a `MirReference_Integer` is equal to a valid
`MirReference`.

## `{Arc,Rc}::{from,into}_inner_raw`

`crucible-mir` is not currently able to simulate the
`{Arc,Rc}::{from,into}_raw` functions. This is because they subtract a constant
offset from a `*T` pointer in order to obtain a pointer of type
`*ArcInner<T>`/`*RcInner<T>`. This sort of pointer arithmetic is permitted in
Rust, but `crucible-mir`'s memory model is not yet sophisticated enough to
support this.

As a workaround, we offer `{Arc,Rc}::{from,into}_inner_raw` API functions,
which work directly on `*ArcInner<T>`/`*RcInner<T>` pointers instead of `*T`
pointers, thereby avoiding the need for problematic pointer casts. This is not
a perfect solution, as these functions will not work as drop-in replacements
for `{Arc,Rc}::{from,into}_raw` in all situations due to the differences in
types. Where they _do_ work as drop-in replacements are situations where a call
to `{Arc,Rc}::into_raw` is followed by another call to `{Arc,Rc}::from_raw`,
without reading the intermediate raw pointer in between. For instance, in the
following example (taken from the [documentation for
`Arc::from_raw`](https://doc.rust-lang.org/1.91.0/std/sync/struct.Arc.html#method.from_raw)):

```rs
use std::sync::Arc;

let x = Arc::new("hello".to_owned());
let x_ptr = Arc::into_raw(x);

unsafe {
    // Convert back to an `Arc` to prevent leak.
    let x = Arc::from_raw(x_ptr);
    assert_eq!(&*x, "hello");

    // Further calls to `Arc::from_raw(x_ptr)` would be memory-unsafe.
}
```

The calls to `Arc::{from,into}_raw` can be replaced with
`Arc::{from,into}_inner_raw` with no change in functionality. This sort of
pattern occurs fairly often in practice, so it is worth having at least some
support for it. For example, the internals of `std::thread` also construct
`Arc` values in a very similar fashion, so we also patch `std::thread` to use
`Arc::{from,into}_inner_raw`.

(An API design note: because `{Arc,Rc}::{from,into}_inner_raw` are exposed as
part of the public API, we must also expose the (previously internal)
`ArcInner` and `RcInner` types as a consequence.)

Once `crucible-mir` finishes migrating to use `MirAggregate` (see
https://github.com/GaloisInc/crucible/issues/1499), it should be able to
simulate `{Arc,Rc}::{from,into}_raw` properly, which would allow us to remove
`{Arc,Rc}::{from,into}_inner_raw`.
