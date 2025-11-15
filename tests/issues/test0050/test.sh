#!/usr/bin/env bash
set -euo pipefail
source "$(dirname "$0")/../../common.sh"

expect_no_panic saw-rustc --version
expect_no_panic saw-rustc --help
expect_no_panic saw-rustc -h
expect_no_panic saw-rustc --print sysroot
expect_no_panic saw-rustc -C help
expect_no_panic saw-rustc --explain E0308
