#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_output_does_not_contain "cannot find module or crate \`crux\` in this scope" \
  mir-json test.rs --crate-type rlib \
    --target "$(rustc --print host-tuple)"
