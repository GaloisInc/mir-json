#!/usr/bin/env bash
set -Eeuxo pipefail

setup_dist_bins() {
  mkdir -p dist/bin
  # Copy over each binary (built with --release) listed in Cargo.toml.
  for bin in $(cargo read-manifest | jq -r '.targets[] | select([ .kind[] | contains("bin") ] | any) | .name'); do
    cp "target/release/$bin" "dist/bin/$bin";
  done
}

zip_dist() {
  name="$1"
  cp -Lr rlibs dist/rlibs
  cp -r dist "$name"
  tar -czf "$name".tar.gz "$name"
}

COMMAND="$1"
shift

"$COMMAND" "$@"
