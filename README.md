Tool to compile rust to MIR, encoded as JSON.

Uses unstable features -- the most recent build which has been
successfully tested is rustc nightly-2019-08-05

## Installation instructions

1. If you are starting from scratch, you need to first install the rust
compiler via the `rustup` tool. (Instructions are from the [rust
book](https://doc.rust-lang.org/book/2018-edition/ch01-01-installation.html)).

       $ curl https://sh.rustup.rs -sSf | sh

    To finish the compiler installation you need to add the tools to your path:

       $ source $HOME/.cargo/env

2. Next, switch your version of `rustc` to the one that works with mir-json.

       $ rustup toolchain install nightly-2019-08-05

       $ rustup default nightly-2019-08-05

3. Now compile `mir-json`

       $ cargo build

4. Then install the `mir-json` executable to your path

       $ cargo install

5. If you want to run `mir-json` directly, add this line to your
`.bash_profile` beforehand

       export LD_LIBRARY_PATH=$(rustc --print sysroot)/lib:$LD_LIBRARY_PATH

   For macOS, add this line instead

       export DYLD_LIBRARY_PATH=$(rustc --print sysroot)/lib:$DYLD_LIBRARY_PATH

6. Check that `mir-json` was installed correctly

       mir-json --version

   It should print a version string.  If it prints a shared library error
   instead, then most likely your `$LD_LIBRARY_PATH` is not set correctly.
