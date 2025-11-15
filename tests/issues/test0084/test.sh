#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

rm -f test.linked-mir.json libtest.mir libtest.rlib test

echo "Testing SAW build (saw-rustc)..."
OUTPUT=$(${SAW_RUSTC} test.rs 2>&1)

# Verify .linked-mir.json file was created
if [ ! -f test.linked-mir.json ]; then
    echo "ERROR: test.linked-mir.json not created"
    exit 1
fi

# Verify test script was NOT created
if [ -e test ]; then
    echo "ERROR: SAW build should not create executable test script"
    exit 1
fi

echo "SAW build correctly skipped test script"

rm -f test.linked-mir.json libtest.mir libtest.rlib

echo "Testing Crux build (crux-rustc)..."
OUTPUT=$(crux-rustc --test test.rs 2>&1)

# Verify .linked-mir.json file was created
if [ ! -f test.linked-mir.json ]; then
    echo "ERROR: test.linked-mir.json not created"
    exit 1
fi

# Verify test script WAS created and is executable
if [ ! -e test ] || [ ! -x test ]; then
    echo "ERROR: Crux build should create executable test script"
    exit 1
fi
