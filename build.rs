use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::str;

fn main() {
    // Add the toolchain lib/ directory to `-L`.  This fixes the linker error "cannot find
    // -lLLVM-13-rust-1.60.0-nightly".
    let out = Command::new("rustup")
        .args(&["which", "rustc"])
        .output().unwrap();
    assert!(out.status.success());
    let rustc_path = Path::new(str::from_utf8(&out.stdout).unwrap().trim_end());
    let lib_dir = rustc_path.parent().unwrap().parent().unwrap().join("lib");
    println!("cargo:rustc-link-search={}", lib_dir.display());

    // On Windows nightly toolchains, rustc-dev and rust-src can both ship
    // getopts with different hashes, causing E0464 (multiple matching crates).
    // Work around by renaming the rust-src copy (the one with an rlib) to .bak.
    // Only target getopts — other duplicates (hashbrown, etc.) are harmless or
    // needed by std.
    if cfg!(target_os = "windows") {
        let sysroot = rustc_path.parent().unwrap().parent().unwrap();
        let target = std::env::var("TARGET").unwrap_or_default();
        let target_lib = sysroot
            .join("lib")
            .join("rustlib")
            .join(&target)
            .join("lib");
        if target_lib.exists() {
            deduplicate_getopts(&target_lib);
        }
    }
}

/// If getopts has multiple rmeta files (different hashes), rename the one
/// that also has an rlib companion to `.bak`.
fn deduplicate_getopts(dir: &Path) {
    let entries: Vec<PathBuf> = match fs::read_dir(dir) {
        Ok(rd) => rd.filter_map(|e| e.ok().map(|e| e.path())).collect(),
        Err(_) => return,
    };

    // Find all getopts rmeta files
    let getopts_rmetas: Vec<&PathBuf> = entries.iter().filter(|p| {
        p.file_name()
            .and_then(|n| n.to_str())
            .map(|n| n.starts_with("libgetopts-") && n.ends_with(".rmeta"))
            .unwrap_or(false)
    }).collect();

    if getopts_rmetas.len() <= 1 {
        return;
    }

    // Rename the copy that has a companion rlib (rust-src copy)
    for rmeta_path in &getopts_rmetas {
        let rlib_path = rmeta_path.with_extension("rlib");
        if rlib_path.exists() {
            let rmeta_bak = PathBuf::from(format!("{}.bak", rmeta_path.display()));
            let rlib_bak = PathBuf::from(format!("{}.bak", rlib_path.display()));
            if !rmeta_bak.exists() {
                eprintln!(
                    "cargo:warning=Renaming duplicate getopts rmeta/rlib to .bak in {}",
                    dir.display()
                );
                let _ = fs::rename(rmeta_path, &rmeta_bak);
                let _ = fs::rename(&rlib_path, &rlib_bak);
            }
        }
    }
}
