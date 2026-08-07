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

# Usage: expect_json_contains <jq-expression> <json-file>
expect_json_contains() {
  if ! jq -e "$1" "$2" > /dev/null; then
    echo "ERROR: jq check failed: $1 on $2"
    exit 1
  fi
}

# Usage: expect_static_matches <name-suffix> <expected-json>
#
# Match the shape of the .statics[] entry ending with <name-suffix> in
# test.linked-mir.json against <expected-json>, ignoring volatile fields.
expect_static_matches() {
  local suffix="$1"
  local expected="$2"
  local file=test.linked-mir.json

  local actual
  actual=$(jq --arg n "$suffix" \
    '.statics[]
       | select(.name | endswith($n))
       | del(.name, .ty, .rendered.def_id, .rendered.element_ty)' \
    "$file")

  if [[ -z "$actual" ]]; then
    echo "ERROR: no .statics[] entry with name ending in '$suffix' in $file"
    exit 1
  fi

  if ! diff <(echo "$expected" | jq -S .) <(echo "$actual" | jq -S .); then
    echo "ERROR: shape of static '$suffix' did not match expected"
    exit 1
  fi
}

expect_output_does_not_contain() {
  set +e
  output=$("${@:2}" 2>&1)
  status=$?
  set -e

  if echo "$output" | grep -q "$1"; then
    echo "Output contains '$1'"
    echo "$output"
    return 1
  fi

  echo "Output does not contain '$1'"
}
