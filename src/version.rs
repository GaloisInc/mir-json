use std::env::Args;

/// The version of the JSON schema that `mir-json` follows. This is intended for
/// use by downstream tools to quickly determine if they are ingesting a MIR
/// JSON file that is compatible with the version of the schema that they are
/// expecting.
///
/// Each version of the schema is assumed to be backwards-incompatible with
/// previous versions of the schema. As such, any time this version number is
/// bumped, it should be treated as a major version bump.
pub const SCHEMA_VER: u64 = 5;

/// Check if the arguments contain version flags ("--version" or "-V").
pub fn has_flag(args: &mut Args) -> bool
{
    args.any(|arg| {
        arg == "--version" ||
        // Combined short flags like -vV
        (arg.starts_with('-') && !arg.starts_with("--") && arg.contains('V'))
    })
}

/// A string containing the mir-json and JSON schema versions.
pub fn string() -> String {
    format!("mir-json {} (JSON schema version {})", env!("CARGO_PKG_VERSION"), SCHEMA_VER)
}
