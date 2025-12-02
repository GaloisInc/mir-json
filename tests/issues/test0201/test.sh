#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

# Fail if the first line of stdout does not correspond to the output of
# `rustc --version`.
expect_rust_version_first_line() {
  set +e
  output=$("$@")
  set -e

  echo "Checking: $@"
  if echo "$output" | head -1 | grep -q 'rustc 1'; then
    echo "rustc --version information detected in the first line of stdout."
    return 0
  fi

  echo "$output"
  echo "No rustc --version information detected in the first line of stdout."
  return 1
}

expect_rust_version_first_line \
  mir-json --version

expect_rust_version_first_line \
  mir-json-rustc-wrapper rustc --target "$(rustc --print host-tuple)" --version

expect_rust_version_first_line \
  crux-rustc --version

expect_rust_version_first_line \
  saw-rustc --version
