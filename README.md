`mir-json` provides `rustc` and `cargo` integration for
[mir-verifier][mir-verifier-repo].

## Installation instructions

1. If you are starting from scratch, you need to first install the rust
compiler via the `rustup` tool. (Instructions are from the [rust
book](https://doc.rust-lang.org/book/2018-edition/ch01-01-installation.html)).

       $ curl https://sh.rustup.rs -sSf | sh

   To finish the compiler installation you need to add the tools to your path:

       $ source $HOME/.cargo/env

2. Next, switch your version of `rustc` to the one that works with mir-json.

       $ rustup toolchain install nightly-2020-03-22 --force
       $ rustup component add --toolchain nightly-2020-03-22 rustc-dev
       $ rustup default nightly-2020-03-22

3. Now compile `mir-json` and install its executables to your path.

       $ RUSTC_WRAPPER=./rustc-rpath.sh cargo install --locked

4. Check that `mir-json` was installed correctly

       mir-json --version

   It should print a version string.  If it prints a shared library error
   instead, then most likely something went wrong with the `rustc-rpath.sh`
   wrapper.  Try running `cargo clean` and repeating step 3, or try setting
   `$LD_LIBRARY_PATH`/`$DYLD_LIBRARY_PATH` to include `$(rustc --print
   sysroot)/lib`.


## Usage

See the [mir-verifier][mir-verifier-repo] README for usage instructions.


[mir-verifier-repo]: https://github.com/GaloisInc/mir-verifier
