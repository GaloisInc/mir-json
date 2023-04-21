`mir-json` provides `rustc` and `cargo` integration for interfacing with
[crux-mir][crux-mir-repo].

## Installation instructions

1. If you are starting from scratch, you need to first install the rust
compiler via the `rustup` tool. (Instructions are from the [rust
book](https://doc.rust-lang.org/book/2018-edition/ch01-01-installation.html)).

       $ curl https://sh.rustup.rs -sSf | sh

   To finish the compiler installation you need to add the tools to your path:

       $ source $HOME/.cargo/env

2. Next, install a version of `rustc` that works with mir-json.

       $ rustup toolchain install nightly-2020-03-22 --force
       $ rustup component add --toolchain nightly-2020-03-22 rustc-dev
       $ rustup default nightly-2020-03-22

   <!-- Note: when changing to a new nightly, also update `wrapper.rs` -->

3. Now compile `mir-json` and install its executables to your path.

       $ cargo install --locked

4. Check that `mir-json` was installed correctly

       $ mir-json --version

   This should print a version string.


## Usage

See the [crux-mir][crux-mir-repo] README for usage instructions.


[crux-mir-repo]: https://github.com/GaloisInc/crucible/tree/master/crux-mir
