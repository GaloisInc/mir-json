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


* Avoid `transmute` in `Layout` and `Alignment` (last applied: September 17, 2026)

  `Alignment::new_unchecked` uses `transmute` to convert an integer to an enum
  value, assuming that the integer is a valid discriminant for the enum.
  `Layout::from_size_align` performs the same `transmute` operation directly,
  bypassing `Alignment::new_unchecked`.  This patch reimplements
  `Alignment::new_unchecked` without `transmute` and modifies `Layout` to call
  it.  Finally, this patch removes a `transmute` in the opposite direction from
  `Alignment::as_usize`.

* Add a hook in `NonZero::new` (last applied: September 17, 2026)

  The new generic `NonZero::new` relies on transmute to convert `u32` to
  `Option<NonZero<u32>>` in a const context.  Removing this transmute is
  difficult due to limited ability to use generics in a const context.
  Instead, we wrap it in a hook that we can override in crucible-mir.

* Disable `BytewiseEq`-based array/slice comparisons (last applied: September 17, 2026)

  These require a special comparison intrinsic (`core::intrinsics::raw_eq`)
  that Crucible doesn't support. We instead fall back on the other
  `SpecArrayEq`/`SlicePartialEq` instances that are slower (but easier to
  translate).

* Use `crucible_cell_swap_is_nonoverlapping_hook` in `Cell::swap` (last applied: September 17, 2026)

  The actual implementation of `cell::swap` checks for overlapping `Cell`
  references before performing the swap and panics if there is overlap. The
  overlap check relies pointer-to-integer casts that `crucible-mir` does not
  currently support. As such, we use a Crucible override for the overlap check.


* Use `crucible::ptr::compare_usize` for pointer-integer comparisons (last applied: September 17, 2026)

  The `is_null` method on pointers works by casting the pointer to an integer
  and comparing to zero.  However, crucible-mir doesn't support casting valid
  pointers to integers (e.g. `&x as *const _ as usize` will always fail).  We
  reimplement `is_null` in terms of `crucible::ptr::compare_usize(ptr, n)`,
  which directly checks whether `ptr` is the result of casting `n` to a pointer
  type.

  The internal function `alloc::rc::is_dangling` is implemented similarly to
  `is_null`, so we reimplement it in terms of `compare_usize` as well.

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
