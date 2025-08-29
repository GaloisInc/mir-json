#!/usr/bin/env bash
set -euo pipefail
export TEST_ROOT=$(dirname "$0")
export MIR_JSON_RLIBS=/mir-json/rlibs
source "$TEST_ROOT/common.sh"

discover_tests() {
  local base="$TEST_ROOT/issues"
  find "$base" -maxdepth 1 -type d -name 'test*' | sort
}

load_disabled_tests() {
  if [[ -n "${DISABLED_TESTS:-}" ]]; then
    echo "$DISABLED_TESTS"
  else
    grep -v '^#' "$TEST_ROOT/disabled_tests.txt" || true
  fi
}

main() {
  local disabled=($(load_disabled_tests))
  local enabled=(${ENABLED_TESTS:-})
  local tests=()

  for tdir in $(discover_tests); do
    tname=$(basename "$tdir")
    if [[ "${#enabled[@]}" -gt 0 && ! " ${enabled[*]} " =~ " $tname " ]]; then
      continue
    fi
    if [[ " ${disabled[*]} " =~ " $tname " ]]; then
      echo "Skipping disabled test $tname"
      continue
    fi
    tests+=("$tdir")
  done

  local failures=0
  for t in "${tests[@]}"; do
    echo "=== Running $t ==="
    if ! (cd "$t" && ./test.sh); then
      echo "FAILED: $t"
      failures=$((failures + 1))
    fi
  done

  if [[ $failures -gt 0 ]]; then
    echo "$failures test(s) failed"
    exit 1
  fi

  echo "All tests passed"
}

main "$@"

