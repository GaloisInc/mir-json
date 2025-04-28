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

* Add a hook for the cast in `std::slice::as_chunks_unchecked(_mut)` (last applied June 9, 2026)

  These functions convert `&[T]` to `&[[T; N]]`, which internally involves a
  cast from `*const T` to `*const [T; N]` that the current crux-mir memory
  model doesn't support in general.  This patch adds a hook for the cast so we
  can implement it using crux-mir's new `AggregateAsChunks_RefPath` feature,
  which is a special case designed specifically for `<[_]>::as_chunks`.

  Given this capability the following functions are then rewritten in terms of
  `as_chunks_unchecked(_mut)`: `first_chunk(_mut)`, `split_first_chunk(_mut)`,
  `last_chunk(_mut)`, `split_last_chunk(_mut)`, `slice::as(_mut)_array`.

  See also the "Limitations of zero-length arrays and
  `slice::as_chunks_unchecked(_mut)`" note below.

* Avoid `transmute` in `Layout` and `Alignment` (last applied: June 9, 2026)

  `Alignment::new_unchecked` uses `transmute` to convert an integer to an enum
  value, assuming that the integer is a valid discriminant for the enum.
  `Layout::from_size_align` performs the same `transmute` operation directly,
  bypassing `Alignment::new_unchecked`.  This patch reimplements
  `Alignment::new_unchecked` without `transmute` and modifies `Layout` to call
  it.  Finally, this patch removes a `transmute` in the opposite direction from
  `Alignment::as_usize`.

* Add a hook in `NonZero::new` (last applied: June 9, 2026)

  The new generic `NonZero::new` relies on transmute to convert `u32` to
  `Option<NonZero<u32>>` in a const context.  Removing this transmute is
  difficult due to limited ability to use generics in a const context.
  Instead, we wrap it in a hook that we can override in crucible-mir.

* Use crucible's allocator in `Box` constructors (last applied: June 9, 2026)

  Rust's allocator API returns untyped memory, similar to `malloc`, and `Box`
  casts the result from `*mut u8` to `*mut T`.  Since crucible-mir works only
  with typed memory, we replace the allocator calls in `Box::new` and related
  functions to call built-in Crucible allocation functions instead (e.g.
  `crucible::alloc::allocate`).

* Specialize `Clone` impl for `Box` to use Crucible's allocator (last applied: June 9, 2026)

  The default `Clone` impl for `Box` is parameterized over an arbitrary
  allocator, and as a result, it has to call the `new_uninit_in` function,
  which `crucible-mir` cannot easily support. We add a specialized version of
  the `Clone` impl for the `Global` allocator that instead calls the more
  Crucible-friendly `new_uninit` function. (See also the `` Use crucible's
  allocator in `Box` constructors `` patch above.)

* Define `Arc`/`Rc` constructors in terms of `{Arc,Rc}::new` (last applied: June 9, 2026)

  This ensures that all `Arc`/`Rc` constructors are defined in terms of
  `Box::new`, which uses Crucible's typed allocator instead of Rust's untyped
  allocator. (See the `` Use crucible's allocator in `Box` constructors ``
  patch above.)

* Don't deallocate in `Box`/`Rc`/`Arc` `drop` methods (last applied: June 9, 2026)

  Crucible doesn't support a `deallocate` operation.

* Make some `Vec` methods non-const (last applied: June 9, 2026)

  Some allocating methods, such as `Vec::with_capacity_in`, can now be used in
  const contexts if the allocator is also const (`A: [const] Allocator`).
  Currently we don't support const usage of `crucible::TypedAllocator<T>`.  For
  now we handle this by making the methods non-const, which works because
  nothing within the standard library relies on them being const.

  If we need to support this properly in the future, we could try making
  `TypedAllocator` dispatch to `alloc::Global` when used in const contexts.
  This should produce static allocations, which mir-json and crucible-mir will
  translate just like those arising from static slices and such.

* Always use `crucible::TypedAllocator` in `RawVecInner` (last applied: June 9, 2026)

  Upstream has polymorphized the `RawVec` implementation by factoring out most
  of the logic into a new `RawVecInner` type that's parameterized only by an
  allocator, not by the element type `T`.  This makes it difficult to switch
  over to crucible-mir's allocation functions, which require the element type.
  This patch modifies `RawVec` to always instantiate `RawVecInner` with
  `crucible::TypedAllocator<T>` as its allocator, which is minimally invasive
  and has the effect of threading the element type through to the crucible-mir
  allocation functions.

# Notes

This section contains more detailed notes about why certain patches are written
the way they are. If you plan to reapply a patch that references one of these
notes, please make sure that the spirit of the note is still upheld in the new
patch. Alternatively, if you choose to deviate from the note, make sure to do
so after carefully considering why deviating is the right choice, and consider
updating the note in the process.

## Mark hook functions as `#[inline(never)]`

We want to ensure that custom hook functions (e.g.,
`crucible_null_hook`) are always present in generated MIR code,
regardless of whether or not optimizations are applied. In some cases, it may
not suffice to compile the code containing the hook functions without
optimizations (as `mir-json-translate-libs` currently does), as `rustc` can
still inline code that is contained in a different compilation unit. (See
[#153](https://github.com/GaloisInc/mir-json/issues/153) for an example where
this actually happened.)

As a safeguard, we mark all custom hook functions as `#[inline(never)]` to
ensure that they persist when optimizations are applied.

## Limitations of zero-length arrays and `slice::as_chunks_unchecked(_mut)`

One of the reasons why we override `slice::as_chunks_unchecked(_mut)` is so
that we can guarantee that the input reference aliases the output reference.
Currently, this requires custom overrides in `crucible-mir` to accomplish.
Moreover, we can define many similar-looking functions in terms of
`slice::as_chunks_unchecked(_mut)`, which allows us to get away with only
defining two custom overrides.

Unfortunately, this approach has a notable drawback. We define functions such
as `slice::as(_mut)_array` in terms of `slice::as_chunks_unchecked(_mut)`, but
while the former functions work for arrays of any length, the latter functions
have a precondition that the array length is non-zero. This means that if we
call `slice::as(_mut)_array` with an array length of zero, then we cannot call
`slice::as_chunks_unchecked(_mut)` and must use a different approach.

One possible way to go about this would be to give `slice::as(_mut)_array` and
friends additional custom overrides to handle the length-0 cases. This is
doable, but it would be annoying to maintain, given that we would need to add a
significant amount of additional special-casing. What's more, we are planning
to remove these special cases later once the migration to `MirAggregate` is
finished (see https://github.com/GaloisInc/crucible/issues/1499), so it feels
wasteful to invest in this kind of solution.

We instead adopt a less correct but much cheaper solution: when the array
length is zero, simply return `&[]` or `&mut []`. This sort of output reference
will _not_ alias the input reference, but since the output has no actual
elements, the lack of aliasing is hard to observe. As such, this compromise is
likely fine for most use cases.
