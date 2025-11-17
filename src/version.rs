use crate::schema_ver::SCHEMA_VER;

use std::env::{self, Args};

/// Check if the arguments contain version flags ("--version" or "-V").
pub fn has_flag(args: &mut Args) -> bool
{
    args.any(|arg| {
        arg == "--version" ||
        // Combined short flags like -vV
        (arg.starts_with('-') && !arg.starts_with("--") && arg.contains('V'))
    })
}

/// A string containing the mir-json version, JSON schema version, and the Rust
/// toolchain version (if set).
pub fn string() -> String {
    let base = format!("mir-json {} (JSON schema version {})",
        env!("CARGO_PKG_VERSION"), SCHEMA_VER);

    if let Ok(toolchain) = env::var("RUSTUP_TOOLCHAIN") {
        format!("{}\nRust toolchain {}", base, toolchain)
    } else {
        base
    }
}

/// Print out the version string.
pub fn show() {
    println!("{}", string());
}
