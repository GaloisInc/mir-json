#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_output_does_not_contain "use of an unstable feature" \
  saw-rustc test.rs \
    --target "$(rustc --print host-tuple)"
