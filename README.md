`mir-json` provides `rustc` and `cargo` integration for interfacing with
[crux-mir][crux-mir-repo].

## Installation instructions

`mir-json` can either be built from source or accessed via a Docker image.

### Building from source

1. First install the rust compiler via the `rustup` tool. (Instructions are
   from the [rust
   book](https://doc.rust-lang.org/book/2018-edition/ch01-01-installation.html)).

       $ curl https://sh.rustup.rs -sSf | sh

   To finish the compiler installation you need to add the tools to your path:

       $ source $HOME/.cargo/env

2. Next, install a version of `rustc` that works with mir-json.

       $ rustup toolchain install nightly-2023-01-23 --force
       $ rustup component add --toolchain nightly-2023-01-23 rustc-dev rust-src
       $ rustup default nightly-2023-01-23

   <!-- Note: when changing to a new nightly, also update `wrapper.rs` -->

3. Now compile `mir-json` and install its executables to your path.

       $ cargo install --locked

4. Check that `mir-json` was installed correctly

       $ mir-json --version

   This should print a version string.

5. Translate the `mir-json`–specific versions of the Rust standard libraries:

       $ ./translate_libs.sh

   This should create an `rlibs` directory. [The documentation](doc/rustc.md)
   contains a more detailed description of different ways to run the
   `translate_libs.sh` script.

6. Define one of the following environment variables:

       CRUX_RUST_LIBRARY_PATH=$(pwd)/rlibs
       SAW_RUST_LIBRARY_PATH=$(pwd)/rlibs

   These tell `mir-json` where to look for the standard libraries. See [the
   documentation](doc/rustc.md) for more information on these environment
   variables.

### Docker image

To pull the Docker image, run:

```
$ docker pull ghcr.io/galoisinc/mir-json
```

This provides an installation of the `mir-json` tools and translated copies of
the `mir-json`–specific Rust standard libraries. Different `mir-json` tools can
be accessed by overriding the Docker entrypoint. For example, in order to run
`crux-rustc`, invoke the following:

```
$ docker run --entrypoint /home/mir-json/.cargo/bin/crux-rustc ghcr.io/galoisinc/mir-json <ARGUMENTS>
```

## Usage

`mir-json` compiles Rust code into a stable on-disk representation that can be
formally reasoned about by tools such as crux-mir and SAW. For more information
on how these tools ingest `mir-json`, refer to the [crux-mir
README][crux-mir-repo] or the [SAW Rust tutorial][saw-rust-tutorial] for usage
instructions.

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
described in the [`SCHEMA_CHANGELOG.md`](SCHEMA_CHANGELOG.md) file.


[crux-mir-repo]: https://github.com/GaloisInc/crucible/tree/master/crux-mir
[saw-rust-tutorial]: https://github.com/GaloisInc/saw-script/blob/master/doc/pdfs/rust-verification-with-saw.pdf
