`mir-json` provides `rustc` and `cargo` integration for interfacing with
[crux-mir][crux-mir-repo].

## Installation instructions

`mir-json` can either be built from source or accessed via a Docker image.

### Building from source

1. First install the Rust compiler by following the instructions here:

       https://rustup.rs/

   To finish the compiler installation, add the tools to your path:

       $ source $HOME/.cargo/env

2. Next, install a version of the Rust toolchain that works with `mir-json`:

       $ rustup toolchain install nightly-2023-01-23 --force --component rustc-dev,rust-src

3. You will need basic build tools like `cc` to compile `mir-json`. On Ubuntu this is sufficient:

       $ sudo apt install build-essential

4. Install `mir-json`:

       $ cargo +nightly-2023-01-23 install --path . --locked

5. Check that `mir-json` was installed correctly:

       $ mir-json --version

   This should print a version string.

6. Translate the `mir-json`–specific versions of the Rust standard libraries:

       $ mir-json-translate-libs

   This should create an `rlibs` directory. [The documentation](doc/rustc.md)
   contains a more detailed description of different ways to run the
   `mir-json-translate-libs` program.

7. Define one of the following environment variables:

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

