#!/usr/bin/env bash

set -e

# If TARGET is not specified, scrape it from the 'host: <target_triple>' line in
# rustc's output
: "${TARGET:=$(rustc --version --verbose | sed -n 's/host: //p')}"

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
RLIBS_PARENT="${SCRIPT_DIR}/rlibs_real"
RLIBS_SYMLINK="${SCRIPT_DIR}/rlibs"
RLIBS=$(rustc --target "$TARGET" --print target-libdir --sysroot "${RLIBS_PARENT}")

# Split target triple on '-' into arch, vendor, and os components
IFS=- read -r TARGET_ARCH _TARGET_VENDOR TARGET_OS <<< "$TARGET"

STD_ENV_ARCH=$TARGET_ARCH
export STD_ENV_ARCH

if [ "$TARGET_ARCH" = "x86_64" ]; then
  IS_X86_64=yes
fi

translate() {
    mir-json --target "$TARGET" -L "${RLIBS}" --out-dir "${RLIBS}" --crate-type rlib --remap-path-prefix "$(pwd -P)=." "$@"
}

mkdir -p "${RLIBS_PARENT}/bin"
mkdir -p "${RLIBS_PARENT}/etc"
mkdir -p "${RLIBS_PARENT}/lib"
mkdir -p "${RLIBS_PARENT}/libexec"
mkdir -p "${RLIBS_PARENT}/share"
mkdir -p "${RLIBS}"
if [ ! -d "${RLIBS_SYMLINK}" ]; then
  ln -s "${RLIBS}" "${RLIBS_SYMLINK}"
fi

echo 'Building core...'
translate libs/core/src/lib.rs --edition=2021 --crate-name core

echo 'Building rustc_std_workspace_core...'
translate libs/rustc_std_workspace_core/lib.rs --edition=2021 --crate-name rustc_std_workspace_core --extern "core=${RLIBS}/libcore.rlib"

echo 'Building libc...'
translate libs/libc/src/lib.rs  --crate-name libc --cfg 'feature="align"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="rustc-std-workspace-core"' --cfg freebsd11 --cfg libc_priv_mod_use --cfg libc_union --cfg libc_const_size_of --cfg libc_align --cfg libc_int128 --cfg libc_core_cvoid --cfg libc_packedN --cfg libc_cfg_target_vendor --cfg libc_non_exhaustive --cfg libc_ptr_addr_of --cfg libc_underscore_const_names --cfg libc_thread_local --cfg 'libc_const_extern_fn`' --extern "rustc_std_workspace_core=${RLIBS}/librustc_std_workspace_core.rlib"

echo 'Building compiler_builtins...'
translate libs/compiler_builtins/src/lib.rs  --crate-name compiler_builtins --cfg 'feature="compiler-builtins"' --cfg 'feature="core"' --cfg 'feature="default"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="unstable"' --cfg 'feature="mem-unaligned"`' --extern "core=${RLIBS}/libcore.rlib"

# extra lib (added manually)
echo "Building crucible..."
translate libs/crucible/lib.rs --crate-name crucible --edition=2021 --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building alloc...'
translate libs/alloc/src/lib.rs --edition=2021 --crate-name alloc --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "crucible=${RLIBS}/libcrucible.rlib"

echo 'Building cfg_if...'
translate libs/cfg_if/src/lib.rs --edition=2018 --crate-name cfg_if --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building memchr...'
translate libs/memchr/src/lib.rs --edition=2018 --crate-name memchr --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' ${IS_X86_64:+ --cfg memchr_runtime_simd --cfg memchr_runtime_sse2 --cfg memchr_runtime_sse42 --cfg 'memchr_runtime_avx`'} --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building adler...'
translate libs/adler/src/lib.rs  --crate-name adler --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building rustc_demangle...'
translate libs/rustc_demangle/src/lib.rs  --crate-name rustc_demangle --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building unwind...'
translate libs/unwind/src/lib.rs --edition=2021 --crate-name unwind --extern "cfg_if=${RLIBS}/libcfg_if.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "libc=${RLIBS}/liblibc.rlib"

echo 'Building panic_unwind...'
translate libs/panic_unwind/src/lib.rs --edition=2021 --crate-name panic_unwind --extern "alloc=${RLIBS}/liballoc.rlib" --extern "cfg_if=${RLIBS}/libcfg_if.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "libc=${RLIBS}/liblibc.rlib" --extern "unwind=${RLIBS}/libunwind.rlib"

echo 'Building rustc_std_workspace_alloc...'
translate libs/rustc_std_workspace_alloc/lib.rs --edition=2021 --crate-name rustc_std_workspace_alloc --extern "alloc=${RLIBS}/liballoc.rlib"

echo 'Building panic_abort...'
translate libs/panic_abort/src/lib.rs --edition=2021 --crate-name panic_abort --extern "alloc=${RLIBS}/liballoc.rlib" --extern "cfg_if=${RLIBS}/libcfg_if.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "libc=${RLIBS}/liblibc.rlib"

echo 'Building gimli...'
translate libs/gimli/src/lib.rs --edition=2018 --crate-name gimli --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="read"' --cfg 'feature="read-core"' --cfg 'feature="rustc-dep-of-std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building std_detect...'
translate libs/std_detect/src/lib.rs --edition=2018 --crate-name std_detect --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="libc"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="std_detect_dlsym_getauxval"' --cfg 'feature="std_detect_file_io"' --extern "cfg_if=${RLIBS}/libcfg_if.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "libc=${RLIBS}/liblibc.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building object...'
translate libs/object/src/lib.rs --edition=2018 --crate-name object --cfg 'feature="alloc"' --cfg 'feature="archive"' --cfg 'feature="coff"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="elf"' --cfg 'feature="macho"' --cfg 'feature="pe"' --cfg 'feature="read_core"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="unaligned"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "memchr=${RLIBS}/libmemchr.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building miniz_oxide...'
translate libs/miniz_oxide/src/lib.rs --edition=2018 --crate-name miniz_oxide --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern "adler=${RLIBS}/libadler.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building hashbrown...'
translate libs/hashbrown/src/lib.rs --edition=2021 --crate-name hashbrown --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="nightly"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="rustc-internal-api"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "core=${RLIBS}/libcore.rlib"

echo 'Building addr2line...'
translate libs/addr2line/src/lib.rs  --crate-name addr2line --cfg 'feature="alloc"' --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "gimli=${RLIBS}/libgimli.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "core=${RLIBS}/libcore.rlib"

# For wasm32 targets which are not emscripten, std depends on dlmalloc because
# the runtime does not provide an allocator. See libs/std/Cargo.toml and
# libs/std/src/sys/wasm/alloc.rs
if [ "$TARGET_ARCH" = "wasm32" ] && [ "$TARGET_OS" != "emscripten" ]; then
  USE_DLMALLOC=yes
  echo 'Building dlmalloc...'
  translate libs/dlmalloc/src/lib.rs --crate-name dlmalloc --cfg 'feature="rustc-dep-of-std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib"
fi

echo 'Building std...'
translate libs/std/src/lib.rs --edition=2021 --crate-name std --cfg 'feature="addr2line"' --cfg 'feature="backtrace"' --cfg 'feature="gimli-symbolize"' --cfg 'feature="miniz_oxide"' --cfg 'feature="object"' --cfg 'feature="panic_unwind"' --cfg 'feature="std_detect_dlsym_getauxval"' --cfg 'feature="std_detect_file_io"' --cfg 'backtrace_in_libstd`' --extern "addr2line=${RLIBS}/libaddr2line.rlib" --extern "alloc=${RLIBS}/liballoc.rlib" --extern "cfg_if=${RLIBS}/libcfg_if.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "hashbrown=${RLIBS}/libhashbrown.rlib" --extern "libc=${RLIBS}/liblibc.rlib" --extern "miniz_oxide=${RLIBS}/libminiz_oxide.rlib" --extern "object=${RLIBS}/libobject.rlib" --extern "panic_abort=${RLIBS}/libpanic_abort.rlib" --extern "panic_unwind=${RLIBS}/libpanic_unwind.rlib" --extern "rustc_demangle=${RLIBS}/librustc_demangle.rlib" --extern "std_detect=${RLIBS}/libstd_detect.rlib" --extern "unwind=${RLIBS}/libunwind.rlib" ${USE_DLMALLOC:+ --extern "dlmalloc=${RLIBS}/libdlmalloc.rlib"}

echo 'Building proc_macro...'
translate libs/proc_macro/src/lib.rs --edition=2021 --crate-name proc_macro --extern "core=${RLIBS}/libcore.rlib" --extern "std=${RLIBS}/libstd.rlib"

echo 'Building unicode_width...'
translate libs/unicode_width/src/lib.rs  --crate-name unicode_width --cfg 'feature="compiler_builtins"' --cfg 'feature="core"' --cfg 'feature="default"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="std"' --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "std=${RLIBS}/libstd.rlib"

echo 'Building getopts...'
translate libs/getopts/src/lib.rs  --crate-name getopts --cfg 'feature="core"' --cfg 'feature="rustc-dep-of-std"' --cfg 'feature="std"' --extern "core=${RLIBS}/libcore.rlib" --extern "std=${RLIBS}/libstd.rlib" --extern "unicode_width=${RLIBS}/libunicode_width.rlib"

echo 'Building test...'
translate libs/test/src/lib.rs --edition=2021 --crate-name test --cfg 'feature="backtrace"' --cfg 'feature="default"' --cfg 'feature="panic-unwind"' --cfg 'feature="std_detect_dlsym_getauxval"' --cfg 'feature="std_detect_file_io"' --extern "cfg_if=${RLIBS}/libcfg_if.rlib" --extern "core=${RLIBS}/libcore.rlib" --extern "getopts=${RLIBS}/libgetopts.rlib" --extern "libc=${RLIBS}/liblibc.rlib" --extern "panic_abort=${RLIBS}/libpanic_abort.rlib" --extern "panic_unwind=${RLIBS}/libpanic_unwind.rlib" --extern "proc_macro=${RLIBS}/libproc_macro.rlib" --extern "std=${RLIBS}/libstd.rlib"

# extra libs (added manually)
echo 'Building int512...'
translate libs/int512.rs --crate-name int512 --extern "core=${RLIBS}/libcore.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib"

echo 'Building bytes...'
translate libs/bytes.rs --edition=2021 --crate-name bytes --extern "core=${RLIBS}/libcore.rlib" --extern "std=${RLIBS}/libstd.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib" --extern "crucible=${RLIBS}/libcrucible.rlib"

echo 'Building byteorder...'
translate libs/byteorder/src/lib.rs --edition=2021 --crate-name byteorder --cfg 'feature="std"' --extern "core=${RLIBS}/libcore.rlib" --extern "std=${RLIBS}/libstd.rlib" --extern "compiler_builtins=${RLIBS}/libcompiler_builtins.rlib"

