#!/bin/sh

crate_type=
next_crate_type=

for arg in "$@"; do
    if [ "$arg" = "--crate-type" ]; then
        next_crate_type=1
    elif [ -n "$next_crate_type" ]; then
        crate_type="$arg"
        next_crate_type=
    fi
done

rustc="$1"

case "$crate_type" in
    *bin*)
        exec "$@" -C link-arg=-Wl,-rpath,"$("$rustc" --print sysroot)/lib"
        ;;
    *)
        exec "$@"
        ;;
esac
