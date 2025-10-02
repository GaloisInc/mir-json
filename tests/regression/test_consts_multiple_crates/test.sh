#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_no_panic cargo saw-build --target "$(rustc --print host-tuple)"
