#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_no_panic saw-rustc test.rs --target "$(rustc --print host-tuple)"
