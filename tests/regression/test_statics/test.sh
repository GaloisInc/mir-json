#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_no_panic saw-rustc test.rs --target "$(rustc --print host-tuple)"

# Target-shape assertions for issue #177. Each static should appear in
# .statics[] as kind:"constant", with `rendered` carrying the
# initializer's ConstVal.
#
# `expect_static_matches` strips volatile fields (`name`, `ty`,
# `rendered.def_id`) before comparing, so these expected values describe
# the *shape* of each static independent of crate-hash and alloc-id churn.

expect_static_matches "::ORDINARY" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "uint", "size": 4, "val": "42" }
}'

expect_static_matches "::MUT_STATIC" '{
  "kind": "constant",
  "mutable": true,
  "rendered": { "kind": "uint", "size": 4, "val": "7" }
}'

# String literal — anonymous {{alloc}} rendered as `strbody`.
expect_static_matches "::STR_REF" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "slice", "len": 2 }
}'

# Nested static via `&const_item` inlining — the outer holds a slice
# pointing at an anonymous nested-static allocation.
expect_static_matches "::NESTED_OUTER" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "slice", "len": 1 }
}'

# Thread-local primitive.
expect_static_matches "::TLS_COUNTER" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "uint", "size": 4, "val": "3" }
}'

# Thread-local reference to a const-promoted literal. Renders as a
# static_ref to the anonymous alloc holding the u32.
expect_static_matches "::TLS_REF" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "static_ref" }
}'

# Slice literal — structurally rendered as an `array` of three bytes.
expect_static_matches "::ARR_REF" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "slice", "len": 3 }
}'

# `static mut` with a compound value — exercises make_allocation_body
# with is_mut = true. Arrays with inline initializers render their
# elements structurally rather than as a slice-into-alloc.
expect_static_matches "::MUT_ARR" '{
  "kind": "constant",
  "mutable": true,
  "rendered": {
    "kind": "array",
    "elements": [
      { "kind": "uint", "size": 4, "val": "1" },
      { "kind": "uint", "size": 4, "val": "2" },
      { "kind": "uint", "size": 4, "val": "3" }
    ]
  }
}'

# Function-pointer static — rendered value points at the callee's DefId.
expect_static_matches "::FN_PTR" '{
  "kind": "constant",
  "mutable": false,
  "rendered": { "kind": "fn_ptr" }
}'

# The callee referenced by FN_PTR must appear in `fns` (populated via
# `mir.used.instances`).
expect_json_contains \
  '.fns[] | select(.name | test("::fn_ptr_target$"))' \
  test.linked-mir.json
