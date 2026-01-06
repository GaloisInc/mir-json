A regression test for [issue
#211](https://github.com/GaloisInc/mir-json/issues/211). This tests
`mir-json`'s ability to compile several types of subtraits that make use of a
supertrait's associated type. Internally, this computes a _projection_ into the
associated type, which must be instantiated with the correct type arguments.
This is surprisingly tricky to get right (as seen in #211), so this tests
various combinations of generic parameters to ensure that the logic for
computing these projections is robust.

All of these examples were minimized from the `syn` crate, which has a
non-trivial trait hierarchy of its own.
