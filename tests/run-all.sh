#!/usr/bin/env bash
set -eo pipefail
export TEST_ROOT=$(dirname "$0")
export MIR_JSON_RLIBS=/mir-json/rlibs
source "$TEST_ROOT/common.sh"

discover_tests() {
  local dirs=("$TEST_ROOT/issues" "$TEST_ROOT/regression")
  for base in "${dirs[@]}"; do
    if [[ -d "$base" ]]; then
      find "$base" -maxdepth 1 -type d -name 'test*'
    fi
  done | sort
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
  local disabled_tests=()
  local failed_tests=()
  local passed_disabled_tests=()
  local failed_disabled_tests=()

  for tdir in $(discover_tests); do
    tname=$(basename "$tdir")
    if [[ "${#enabled[@]}" -gt 0 && ! " ${enabled[*]} " =~ " $tname " ]]; then
      continue
    fi
    if [[ " ${disabled[*]} " =~ " $tname " ]]; then
      echo "Skipping disabled test $tname"
      disabled_tests+=("$tdir")
      continue
    fi
    tests+=("$tdir")
  done

  local failures=0
  for t in "${tests[@]}"; do
    echo "=== Running $t ==="
    if ! (cd "$t" && ./test.sh); then
      echo "FAILED: $t"
      failed_tests+=("$t")
      failures=$((failures + 1))
    fi
  done

  if [[ $failures -gt 0 ]]; then
    echo "$failures test(s) failed"
  fi

  # Run disabled tests, but don't fail CI
  echo "=== Running disabled tests ==="
  for t in "${disabled_tests[@]}"; do
    echo "=== (Disabled) Running $t ==="
    if (cd "$t" && ./test.sh); then
      echo "DISABLED TEST PASSED: $t"
      passed_disabled_tests+=("$t")
    else
      echo "Disabled test failed (as expected): $t"
      failed_disabled_tests+=("$t")
    fi
  done

  echo
  echo "========== EXECUTIVE SUMMARY =========="
  echo "Enabled tests:"
  if [[ ${#failed_tests[@]} -eq 0 ]]; then
    echo "  All enabled tests passed."
  else
    echo "  The following enabled tests failed:"
    for t in "${failed_tests[@]}"; do
      echo "    $t"
    done
  fi

  echo
  echo "Disabled tests:"
  if [[ ${#disabled_tests[@]} -eq 0 ]]; then
    echo "  No disabled tests were present."
  elif [[ ${#passed_disabled_tests[@]} -eq 0 ]]; then
    echo "  All disabled tests failed as expected."
  else
    echo "  The following disabled tests unexpectedly PASSED:"
    for t in "${passed_disabled_tests[@]}"; do
      echo "    $t"
    done
  fi

  if [[ $failures -gt 0 ]]; then
    exit 1
  fi
  if [[ ${#passed_disabled_tests[@]} -gt 0 ]]; then
    exit 2
  fi
}

main "$@"
