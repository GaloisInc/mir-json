#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

# First, check that mir-json can compile the program without panicking.
expect_no_panic \
  saw-rustc test.rs \
    --target "$(rustc --print host-tuple)"

# Next, check that every constant (which is a reference with a non-zero offset)
# is rendered as "unsupported". Full support for constant references with
# non-zero offsets is left as future work (see
# https://github.com/GaloisInc/mir-json/issues/241), so if we add support for
# these in the future, this part of test will need to be updated.
expect_json_contains \
  '.statics | map(.rendered.kind) | all(. == "unsupported")' \
  test.linked-mir.json
