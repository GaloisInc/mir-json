Tool to compile rust to MIR, encoded as JSON.

Uses unstable features -- the most recent build which has been
successfully tested is rustc nightly-2017-08-16.

#####

(Installation instructions if you are new to Rust)

1. If you are starting from scratch, you need to first install the rust compiler via
the `rustup` tool. (Instructions are from the [rust book](https://doc.rust-lang.org/book/2018-edition/ch01-01-installation.html)).

     $ curl https://sh.rustup.rs -sSf | sh

To finish the compiler installation you need to add the tools to your path:

     $ source $HOME/.cargo/env

2. Next, switch your version of `rustc` to the one that works with mir-json.

     $ rustup toolchain install nightly-2017-08-16
     
     $ rustup default nightly-2017-08-16

3. Now compile mir-json

     $ cargo build

4. Then install the executable to your path

     $ cargo install
     