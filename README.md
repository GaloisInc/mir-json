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

       $ rustup toolchain install nightly-2023-01-23 --force
       $ rustup component add --toolchain nightly-2023-01-23 rustc-dev
       $ rustup default nightly-2023-01-23

   <!-- Note: when changing to a new nightly, also update `wrapper.rs` -->

3. Now compile `mir-json` and install its executables to your path.

       $ cargo install --locked

4. Check that `mir-json` was installed correctly

       $ mir-json --version

   This should print a version string.


## Usage

See the [crux-mir][crux-mir-repo] README for usage instructions.

## JSON schema

`mir-json` and related tools produce MIR JSON files as output, which the
contain the intermediate MIR code from the compiled program in a
machine-readable format. Downstream tools are sensitive to the particular
schema that a MIR JSON file uses, so we explicitly record the version of the
JSON schema in each MIR JSON file (in the `"version"` field).

Any time that `mir-json` is updated such that the JSON schema must also be
changed, we will also update the schema version number. The version number is
represented as a single integer. Any changes to the schema are assumed to be
backwards-incompatible with previous versions of the schema, so all version
bumps should be treated as major version bumps. Each change to the schema is
described in the [`SCHEMA_VERSIONING.md`](SCHEMA_VERSIONING.md) file.


[crux-mir-repo]: https://github.com/GaloisInc/crucible/tree/master/crux-mir
