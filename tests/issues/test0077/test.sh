#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

# Fail if no version string.
expect_version() {
  set +e
  output=$("$@" 2>&1)
  set -e

  echo "Checking: $@"
  if echo "$output" | grep -Eq 'mir-json [0-9\.]+ \(JSON schema version [0-9\.]+\)'; then
    echo "Version string detected."
    return 0
  fi

  echo "$output"
  echo "No version string detected."
  return 1
}

expect_version \
  saw-rustc --version

expect_version \
  saw-rustc -V

expect_version \
  saw-rustc -vV

expect_version \
  cargo-mir-json --version

expect_version \
  crux-rustc --version

expect_version \
  mir-json --version

expect_version \
  mir-json-callgraph --version

expect_version \
  mir-json-dce --version

expect_version \
  mir-json-rustc-wrapper rustc --target "$(rustc --print host-tuple)" --version

expect_version \
  mir-json-translate-libs --version
