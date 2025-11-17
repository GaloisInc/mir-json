use crate::schema_ver::SCHEMA_VER;

use std::env::Args;

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

/// Print out the version string.
pub fn show() {
    println!("{}", string());
}
