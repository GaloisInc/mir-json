#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_no_panic saw-rustc test.rs --target "$(rustc -vV | awk '/host:/ {print $2}')"

expect_json_contains \
  '.fns[] | select(.name | test("::call_foo$"))' \
  test.linked-mir.json
