#!/usr/bin/env bash

# Default tool locations; override in CI
export MIR_JSON="${MIR_JSON:-mir-json}"
export SAW_RUSTC="${SAW_RUSTC:-saw-rustc}"

# Fail if a command panics
expect_no_panic() {
  set +e
  output=$("$@" 2>&1)
  status=$?
  set -e

  if echo "$output" | grep -q 'panicked at'; then
    echo "Panic detected"
    echo "$output"
    return 1
  fi

  if [[ $status -ne 0 ]]; then
    echo "Non-zero exit: $status"
    echo "$output"
    return 1
  fi

  echo "No panic"
}
