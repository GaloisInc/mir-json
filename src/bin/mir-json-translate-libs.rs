//! Script which uses `cargo test -Z build-std` to generate or execute
//! `mir-json` commands that build the modified standard libraries.

#![feature(rustc_private)]

extern crate cargo_metadata;
extern crate rustc_driver;
extern crate rustc_session;
extern crate serde;
extern crate shell_escape;
extern crate tempfile;

use std::{
    collections::HashMap,
    convert::TryInto,
    env, fmt, fs,
    io::BufReader,
    os::unix,
    process::{Command, Stdio},
};

use cargo_metadata::{
    camino::{Utf8Path, Utf8PathBuf},
    Artifact, Edition, Message, Target,
};
use serde::Deserialize;
use shell_escape::escape;
use tempfile::TempDir;

const EXTRA_LIB_CRUCIBLE: &str = "crucible";
const EXTRA_LIB_CRUCIBLE_PROC_MACROS: &str = "crucible_proc_macros";
const EXTRA_LIB_INT512: &str = "int512";
const EXTRA_LIB_BYTES: &str = "bytes";
const EXTRA_LIB_BYTEORDER: &str = "byteorder";

/// Name of the new empty cargo project to be created to run `cargo test -Z
/// build-std` in.
const EMPTY_PROJECT_NAME: &str = "mir-json-translate-libs-empty-project";

#[cfg(target_os = "macos")]
const PROC_MACRO_EXTENSION: &str = "dylib";
#[cfg(not(target_os = "macos"))]
const PROC_MACRO_EXTENSION: &str = "so";

/// Deserialized form of cargo --unit-graph JSON output.
/// See https://doc.rust-lang.org/cargo/reference/unstable.html#unit-graph
#[derive(Debug, Deserialize)]
struct UnitGraph {
    version: u32,
    units: Vec<UnitGraphUnit>,
    roots: Vec<usize>,
}

#[derive(Debug, Deserialize)]
struct UnitGraphUnit {
    /// This is not `PackageId` since its format is incompatible with the one
    /// from cargo metadata. This has been fixed in
    /// https://github.com/rust-lang/cargo/pull/15447, so the next time we
    /// upgrade the Rust version we can change this back to `PackageId` and key
    /// `artifact_outputs` with it instead of `src_path`.
    pkg_id: String,
    target: Target,
    #[serde(default)]
    is_std: bool,
    dependencies: Vec<UnitGraphDependency>,
}

#[derive(Clone, Debug, Deserialize)]
struct UnitGraphDependency {
    index: usize,
    extern_crate_name: CrateName,
}

/// Module to hide field of newtype [CrateName].
mod crate_name {
    use std::fmt;
    use std::ops::Deref;

    use serde::Deserialize;

    /// Newtype wrapper around [String] which enforces that all `-` are replaced
    /// with `_`. Package names often contain `-`, but it is not a valid
    /// character in Rust identifiers, and crate names must be valid Rust
    /// identifiers since they are automatically exposed as module names in Rust
    /// code. Therefore cargo converts `-` to `_` when deriving crate names from
    /// package names.
    ///
    /// Construct with [From<&str>].
    #[derive(Clone, Debug, Deserialize, PartialEq)]
    pub struct CrateName(String);

    impl From<&str> for CrateName {
        fn from(name: &str) -> Self {
            Self(name.replace("-", "_"))
        }
    }

    impl From<CrateName> for String {
        fn from(crate_name: CrateName) -> String {
            crate_name.0
        }
    }

    impl fmt::Display for CrateName {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.0.fmt(f)
        }
    }

    impl Deref for CrateName {
        type Target = str;
        fn deref(&self) -> &str {
            &self.0
        }
    }
}
use crate_name::CrateName;

/// Our version of the unit graph, which allows for adding our custom libraries
/// and easily converting to mir-json commands.
struct CustomUnitGraph {
    units: Vec<CustomUnit>,
    roots: Vec<usize>,
}

struct CustomUnit {
    target: CustomTarget<CustomTargetLib>,
    dependencies: Vec<UnitGraphDependency>,
}

enum CustomTarget<L> {
    /// A library to be compiled for the target architecture. We really only
    /// care about the target information for these, so only this variant has
    /// fields.
    TargetLib(L),
    /// A dependency to be compiled for the host, like a build script or proc
    /// macro.
    HostDep,
    /// A binary that is not a [CustomTarget::HostDep].
    FinalBin,
}

impl<L> CustomTarget<L> {
    /// Map inside [CustomTarget::TargetLib].
    fn map_lib<M, F>(self, f: F) -> CustomTarget<M>
    where
        F: FnOnce(L) -> M,
    {
        match self {
            CustomTarget::TargetLib(lib) => CustomTarget::TargetLib(f(lib)),
            CustomTarget::HostDep => CustomTarget::HostDep,
            CustomTarget::FinalBin => CustomTarget::FinalBin,
        }
    }
}

/// The fields here are a combination of the fields we care about from [Target],
/// [cargo_metadata::Artifact], and [cargo_metadata::BuildScript]. Each
/// corresponds to some input to `rustc`.
#[derive(Clone)]
struct CustomTargetLib {
    /// `--crate-name`
    crate_name: CrateName,
    /// source file argument
    src_path: Utf8PathBuf,
    /// `--edition`
    edition: Edition,
    /// `-l`
    linked_libs: Vec<Utf8PathBuf>,
    /// `-L`
    linked_paths: Vec<Utf8PathBuf>,
    /// `--cfg`
    cfgs: Vec<String>,
    /// environment variables
    env: Vec<(String, String)>,
    /// Whether this library is one of the standard libraries (not necessarily
    /// `std` specifically). Used to determine whether to pass
    /// standard-library-specific flags.
    is_stdlib: bool,
}

impl CustomTarget<CustomTargetLib> {
    fn is_target_lib_with_crate_name(&self, crate_name: &CrateName) -> bool {
        match self {
            Self::TargetLib(lib) if lib.crate_name == *crate_name => true,
            _ => false,
        }
    }
}

/// Classify the given [Target] as one of the [CustomTarget] variants.
fn custom_kind_of_target(target: &Target) -> CustomTarget<()> {
    if target.is_custom_build()
        || target.crate_types.iter().any(|t| t == "proc-macro")
    {
        CustomTarget::HostDep
    } else if target.crate_types.iter().any(|t| t == "bin") {
        CustomTarget::FinalBin
    } else {
        CustomTarget::TargetLib(())
    }
}

/// Info about a library's source location.
struct LibPathInfo<'a> {
    /// The artifact output corresponding to the library.
    artifact: &'a Artifact,
    /// The directory of the library's original source (specifically, the
    /// directory of its Cargo.toml).
    orig_pkg_dir: &'a Utf8Path,
    /// The directory of the library's custom (patched) source.
    custom_pkg_dir: Utf8PathBuf,
}

impl UnitGraphUnit {
    /// If it is a library, compute [LibPathInfo] for this unit with the given
    /// artifact output map and custom sources directory.
    fn get_pkg_path_info<'a>(
        &self,
        artifact_outputs: &'a HashMap<Utf8PathBuf, Artifact>,
        sources_dir: &Utf8Path,
    ) -> CustomTarget<LibPathInfo<'a>> {
        custom_kind_of_target(&self.target).map_lib(|()| {
            let artifact = artifact_outputs
                .get(&self.target.src_path)
                .unwrap_or_else(|| {
                    panic!(
                        "library {} (src_path {}) \
                        should have a compiler artifact",
                        self.pkg_id, self.target.src_path
                    )
                });
            LibPathInfo {
                artifact,
                orig_pkg_dir: artifact
                    .manifest_path
                    .parent()
                    .expect("manifest path should be a file"),
                custom_pkg_dir: sources_dir.join(&self.target.name),
            }
        })
    }
}

/// A library that will be compiled by mir-json.
struct MirJsonLib {
    target: CustomTargetLib,
    /// `(x, y)` is passed as `--extern x=liby.rlib`. For this program usually
    /// `x` is the same as `y` but not always.
    dependencies: Vec<(CrateName, String)>,
}

impl CustomUnitGraph {
    /// Find an existing unit with the given crate name and return a
    /// [UnitGraphDependency] referring to it.
    fn get_unit_as_dep(&self, crate_name: CrateName) -> UnitGraphDependency {
        UnitGraphDependency {
            index: self
                .units
                .iter()
                .position(|u| {
                    u.target.is_target_lib_with_crate_name(&crate_name)
                })
                .unwrap_or_else(|| {
                    panic!("library {} should be in unit graph", crate_name)
                }),
            extern_crate_name: crate_name,
        }
    }

    /// Get a mutable reference to an existing unit with the given crate name.
    fn get_unit_mut(&mut self, crate_name: &CrateName) -> &mut CustomUnit {
        self.units
            .iter_mut()
            .find(|u| u.target.is_target_lib_with_crate_name(crate_name))
            .unwrap_or_else(|| {
                panic!("library {} should be in unit graph", crate_name)
            })
    }

    /// Add a new unit and return a [UnitGraphDependency] referring to it.
    fn push_unit_as_dep(
        &mut self,
        lib: CustomTargetLib,
        dependencies: Vec<UnitGraphDependency>,
    ) -> UnitGraphDependency {
        UnitGraphDependency {
            extern_crate_name: lib.crate_name.clone(),
            index: self.push_unit(CustomUnit {
                target: CustomTarget::TargetLib(lib),
                dependencies,
            }),
        }
    }

    /// Add a new unit and mark it as a root.
    fn push_unit_as_root(&mut self, unit: CustomUnit) {
        let index = self.push_unit(unit);
        self.roots.push(index);
    }

    /// Add a new unit.
    fn push_unit(&mut self, unit: CustomUnit) -> usize {
        let index = self.units.len();
        self.units.push(unit);
        index
    }

    /// Compute a topological sort of the unit graph, only including libraries
    /// that should be compiled by mir-json.
    fn sequence_libs(&self) -> Vec<MirJsonLib> {
        let mut result = Vec::new();
        // Cache for the result of the visit function.
        let mut visited: Vec<Option<Option<&CrateName>>> =
            vec![None; self.units.len()];

        /// Process the unit at index `i`. Return its crate name if it should be
        /// included as a dependency, or [None] otherwise.
        fn visit<'a>(
            units: &'a [CustomUnit],
            result: &mut Vec<MirJsonLib>,
            visited: &mut [Option<Option<&'a CrateName>>],
            i: usize,
        ) -> Option<&'a CrateName> {
            if let Some(r) = visited[i] {
                return r;
            }
            let r = match &units[i].target {
                CustomTarget::TargetLib(lib) => {
                    // Visit all dependencies and add this unit to result.
                    let mut lib_deps = Vec::new();
                    for dep in &units[i].dependencies {
                        if let Some(real_crate_name) =
                            visit(units, result, visited, dep.index)
                        {
                            lib_deps.push((
                                dep.extern_crate_name.clone(),
                                real_crate_name.to_string(),
                            ));
                        }
                    }
                    result.push(MirJsonLib {
                        target: lib.clone(),
                        dependencies: lib_deps,
                    });
                    Some(&lib.crate_name)
                }
                CustomTarget::HostDep => {
                    // Do not visit dependencies and do not add this unit to
                    // result.
                    None
                }
                CustomTarget::FinalBin => {
                    // Visit all dependencies but do not add this unit to
                    // result.
                    for dep in &units[i].dependencies {
                        visit(units, result, visited, dep.index);
                    }
                    None
                }
            };
            visited[i] = Some(r);
            r
        }

        for root in &self.roots {
            visit(&self.units, &mut result, &mut visited, *root);
        }

        result
    }
}

/// A representation of a command that can be easily formatted as a shell
/// command or turned into an actual [Command].
struct CmdInvocation {
    program: String,
    args: Vec<String>,
    env: Vec<(String, String)>,
}

impl CmdInvocation {
    fn as_command(&self) -> Command {
        let mut cmd = Command::new(&self.program);
        cmd.args(&self.args)
            // convert iterator items from &(String, String) to
            // (&String, &String)
            .envs(self.env.iter().map(|&(ref k, ref v)| (k, v)));
        cmd
    }
}

impl fmt::Display for CmdInvocation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (k, v) in &self.env {
            write!(f, "{}={} ", k, escape(v.into()))?;
        }
        write!(f, "{}", self.program)?;
        for arg in &self.args {
            write!(f, " {}", escape(arg.into()))?;
        }
        Ok(())
    }
}

fn main() {
    let cwd: Utf8PathBuf = env::current_dir()
        .expect("cwd should be accessible")
        .try_into()
        .expect("cwd should be UTF-8");
    let arg_matches = clap::Command::new("mir-json-translate-libs")
        .bin_name("mir-json-translate-libs")
        .about("Build the custom Rust standard libraries for mir-json")
        .args([
            clap::Arg::new("libs").help(
                "Directory containing custom Rust standard libraries \
                [default: ./libs]",
            ),
            clap::Arg::new("out-dir")
                .short('o')
                .long("out-dir")
                .value_name("OUT_DIR")
                .help(
                    "Directory to place rlibs and rlibs_real in \
                    [default: next to libs]",
                ),
            clap::Arg::new("target")
                .long("target")
                .value_name("TARGET")
                .default_value(rustc_session::config::host_tuple())
                .help("Rust target triple to configure the libraries for"),
            clap::Arg::new("generate").long("generate").help(
                "Print a shell script instead of actually running the build",
            ),
            clap::Arg::new("debug")
                .long("debug")
                .help("Emit debug output on stderr"),
            clap::Arg::new("keep-temp-build")
                .long("keep-temp-build")
                .help(
                    "Persist the temporary cargo package created to run \
                    `cargo test -Z build-std` to out-dir",
                ),
            clap::Arg::new("copy-sources")
                .long("copy-sources")
                .value_name("NEW_LIBS")
                .help(
                    "Instead of translating the existing custom standard \
                    libraries, copy all upstream standard library sources to \
                    NEW_LIBS (if they don't already exist there) and exit \
                    (used for upgrading Rust toolchain)",
                ),
        ])
        .get_matches();
    let custom_sources_dir = match arg_matches.value_of("libs") {
        Some(path) => fs::canonicalize(path)
            .expect("libs should be a valid path")
            .try_into()
            .expect("libs should be UTF-8"),
        None => cwd.join("libs"),
    };
    let out_dir = match arg_matches.value_of("out-dir") {
        Some(path) => path.into(),
        None => custom_sources_dir
            .parent()
            .expect("libs should not be root"),
    };
    let target_triple = arg_matches.value_of("target").unwrap();
    let generate_only = arg_matches.is_present("generate");
    let debug_enabled = arg_matches.is_present("debug");
    let keep_temp_build = arg_matches.is_present("keep-temp-build");
    let new_sources_dir = arg_matches
        .value_of("copy-sources")
        .map(|path| out_dir.join(path));

    // Compute the paths that we will use later to store the build artifacts,
    // but don't actually create them yet.
    eprintln!("Querying paths...");
    let rlibs_sysroot = out_dir.join("rlibs_real");
    let rlibs_symlink = out_dir.join("rlibs");
    let rlibs_dir = Command::new("rustc")
        .arg("--target")
        .arg(target_triple)
        .arg("--print")
        .arg("target-libdir")
        .arg("--sysroot")
        .arg(&rlibs_sysroot)
        .output()
        .expect("rustc --print target-libdir should run")
        .stdout;
    let rlibs_dir: &Utf8Path = std::str::from_utf8(&rlibs_dir)
        .expect("rustc target-libdir should be UTF-8")
        .trim_end()
        .into();

    // Set up a new cargo project for running `cargo test -Z build-std`.
    eprintln!("Creating empty cargo package...");
    let empty_project_dir = {
        let mut builder = tempfile::Builder::new();
        let prefix = EMPTY_PROJECT_NAME.to_owned() + "-";
        builder.prefix(&prefix);
        if keep_temp_build {
            builder.keep(true);
            fs::create_dir_all(out_dir)
                .expect("creating out_dir should succeed");
            builder.tempdir_in(out_dir)
        } else {
            builder.tempdir()
        }
        .expect("temporary directory should be able to be created")
    };
    eprintln!(
        "Empty cargo package path: {}",
        empty_project_dir.path().display()
    );
    let cargo_init_status = Command::new("cargo")
        .current_dir(&empty_project_dir)
        .arg("init")
        .arg("--name")
        .arg(EMPTY_PROJECT_NAME)
        .arg("--vcs")
        .arg("none")
        .status()
        .expect("cargo init should run");
    if !cargo_init_status.success() {
        panic!("cargo init exited with {}", cargo_init_status);
    }

    // Run `cargo test -Z build-std` to obtain compiler artifact and build
    // script result messages.
    eprintln!("Running cargo test...");
    let mut cargo_test_child = {
        let mut cmd = cargo_test_cmd(&empty_project_dir, target_triple);
        cmd.arg("--message-format").arg("json")
            .arg("--no-run")
            // Hack: When cross-compiling, cargo test will fail without an
            // appropriate linker installed. But we only care about compiling
            // the std libraries to rlibs, which rustc can do on its own. So we
            // pass a dummy linker to get cargo test to succeed at the end
            // without actually doing any linking. This has the side benefit of
            // making non-cross builds faster as well by skipping the linking
            // step. Note that "true" here is the program /usr/bin/true (or
            // similar), not just enabling the flag.
            .env("RUSTFLAGS", "-C linker=true");
        if debug_enabled {
            cmd.arg("--verbose");
        }
        cmd.stdout(Stdio::piped())
            .spawn()
            .expect("cargo test should run")
    };
    let cargo_test_child_stdout = cargo_test_child
        .stdout
        .take()
        .expect("cargo test stdout should be captured");
    let cargo_test_child_stdout = BufReader::new(cargo_test_child_stdout);
    let mut artifact_outputs = HashMap::new();
    let mut build_script_outputs = HashMap::new();
    for msg in Message::parse_stream(cargo_test_child_stdout) {
        let msg = msg.expect("reading cargo test output should succeed");
        if debug_enabled {
            eprintln!("Received cargo test message:\n{:#?}", msg);
        }
        match msg {
            Message::CompilerArtifact(art) => {
                if let CustomTarget::TargetLib(()) =
                    custom_kind_of_target(&art.target)
                {
                    artifact_outputs.insert(art.target.src_path.clone(), art);
                }
            }
            Message::BuildScriptExecuted(bs) => {
                build_script_outputs.insert(bs.package_id.clone(), bs);
            }
            _ => {}
        }
    }
    let cargo_test_child_status =
        cargo_test_child.wait().expect("cargo test should have run");
    if !cargo_test_child_status.success() {
        panic!("cargo test exited with {}", cargo_test_child_status);
    }
    if debug_enabled {
        eprintln!("artifact outputs:\n{:#?}", artifact_outputs);
        eprintln!("build script outputs:\n{:#?}", build_script_outputs);
    }

    // Run `cargo test -Z build-std --unit-graph` to obtain unit graph.
    eprintln!("Running cargo --unit-graph...");
    let unit_graph = cargo_test_cmd(&empty_project_dir, target_triple)
        .arg("-Z")
        .arg("unstable-options")
        .arg("--unit-graph")
        .output()
        .expect("cargo --unit-graph should run")
        .stdout;
    let unit_graph: UnitGraph = serde_json::from_slice(&unit_graph)
        .expect("cargo --unit-graph output should match JSON schema");
    if unit_graph.version != 1 {
        panic!(
            "expecting version 1, got version {} of cargo --unit-graph output",
            unit_graph.version
        );
    }
    if debug_enabled {
        eprintln!("cargo unit graph:\n{:#?}", unit_graph);
    }

    // If in copy-sources mode, copy the sources then exit
    if let Some(new_sources_dir) = new_sources_dir {
        fs::create_dir_all(&new_sources_dir)
            .expect("creating copy-sources directory should succeed");
        fn copy(orig_dir: &Utf8Path, custom_dir: &Utf8Path) {
            if fs::exists(custom_dir)
                .expect("copy-sources directory should be accessible")
            {
                eprintln!(
                    "Skipping {}, {} already exists",
                    orig_dir, custom_dir
                );
            } else {
                eprintln!("Copying {} to {}", orig_dir, custom_dir);
                copy_dir(orig_dir, custom_dir);
            }
        }
        for unit in &unit_graph.units {
            if let CustomTarget::TargetLib(path_info) =
                unit.get_pkg_path_info(&artifact_outputs, &new_sources_dir)
            {
                copy(path_info.orig_pkg_dir, &path_info.custom_pkg_dir);
                // These modules are located outside of the `core`/`std` source
                // tree but compiled together with `core`/`std` using #[path],
                // so they don't show up in the unit graph and we have to add
                // them manually. `core`/`std` expects them to be located
                // alongside `core`/`std`.
                if unit.target.name == "core" {
                    copy(
                        &path_info.orig_pkg_dir.with_file_name("stdarch"),
                        &path_info.custom_pkg_dir.with_file_name("stdarch"),
                    );
                    copy(
                        &path_info.orig_pkg_dir.with_file_name("portable-simd"),
                        &path_info
                            .custom_pkg_dir
                            .with_file_name("portable-simd"),
                    );
                } else if unit.target.name == "std" {
                    copy(
                        &path_info.orig_pkg_dir.with_file_name("backtrace"),
                        &path_info.custom_pkg_dir.with_file_name("backtrace"),
                    );
                }
            }
        }
        eprintln!("Remember to add extra libs (e.g. crucible)!");
        return;
    }

    // Process the unit graph, rewriting source file paths to point to our
    // patched versions of the standard library sources, and incorporating
    // information from artifact and build script result messages.
    eprintln!("Processing unit graph...");
    let convert_unit = |unit: UnitGraphUnit| CustomUnit {
        target: unit
            .get_pkg_path_info(&artifact_outputs, &custom_sources_dir)
            .map_lib(|path_info| {
                // Compute the patched source file path by finding the original
                // file's relative path to its package directory, then joining
                // that with our patched package directory.
                let rel_src_path = unit
                    .target
                    .src_path
                    .strip_prefix(path_info.orig_pkg_dir)
                    .expect(
                        "source file should be inside directory of Cargo.toml",
                    );
                let (linked_libs, linked_paths, cfgs, env) =
                    match build_script_outputs
                        .remove(&path_info.artifact.package_id)
                    {
                        Some(bs) => {
                            // Certain packages rely on `cargo` defining the
                            // `OUT_DIR` environment variable (e.g.,
                            // compiler_builtins on AArch64 Linux) in order to
                            // compile.
                            let mut env = bs.env;
                            env.push(("OUT_DIR".into(), bs.out_dir.into()));
                            (bs.linked_libs, bs.linked_paths, bs.cfgs, env)
                        }
                        None => (vec![], vec![], vec![], vec![]),
                    };
                CustomTargetLib {
                    crate_name: unit.target.name.as_str().into(),
                    src_path: path_info.custom_pkg_dir.join(rel_src_path),
                    edition: unit.target.edition,
                    linked_libs,
                    linked_paths,
                    // The build script's outputted cfgs does not include
                    // features automatically computed by cargo, so we add them
                    // in here. Technically we can get them either from the unit
                    // graph or the artifact message, but we use the artifact
                    // message version because it is closer to an actual
                    // invocation of rustc. Not sure if there is actually a
                    // difference.
                    cfgs: path_info
                        .artifact
                        .features
                        .iter()
                        .map(|f| format!("feature=\"{f}\""))
                        .chain(cfgs)
                        .collect(),
                    env,
                    is_stdlib: unit.is_std,
                }
            }),
        dependencies: unit.dependencies,
    };

    let mut custom_graph = CustomUnitGraph {
        units: unit_graph.units.into_iter().map(convert_unit).collect(),
        roots: unit_graph.roots,
    };

    // Add our extra libraries to the unit graph.

    let dep_core = custom_graph.get_unit_as_dep("core".into());
    let dep_compiler_builtins =
        custom_graph.get_unit_as_dep("compiler_builtins".into());
    let dep_std = custom_graph.get_unit_as_dep("std".into());

    // Add crucible
    let dep_crucible = custom_graph.push_unit_as_dep(
        CustomTargetLib {
            crate_name: EXTRA_LIB_CRUCIBLE.into(),
            src_path: [
                custom_sources_dir.as_path(),
                "crucible".into(),
                "lib.rs".into(),
            ]
            .iter()
            .collect(),
            edition: Edition::E2021,
            linked_libs: vec![],
            linked_paths: vec![],
            cfgs: vec![],
            env: vec![],
            is_stdlib: false,
        },
        vec![dep_compiler_builtins.clone(), dep_core.clone()],
    );

    // Add crucible as a dependency of alloc
    custom_graph
        .get_unit_mut(&"alloc".into())
        .dependencies
        .push(dep_crucible.clone());

    // Add int512
    custom_graph.push_unit_as_root(CustomUnit {
        target: CustomTarget::TargetLib(CustomTargetLib {
            crate_name: EXTRA_LIB_INT512.into(),
            src_path: custom_sources_dir.join("int512.rs"),
            edition: Default::default(),
            linked_libs: vec![],
            linked_paths: vec![],
            cfgs: vec![],
            env: vec![],
            is_stdlib: false,
        }),
        dependencies: vec![dep_core.clone(), dep_compiler_builtins.clone()],
    });

    // Add bytes
    custom_graph.push_unit_as_root(CustomUnit {
        target: CustomTarget::TargetLib(CustomTargetLib {
            crate_name: EXTRA_LIB_BYTES.into(),
            src_path: custom_sources_dir.join("bytes.rs"),
            edition: Edition::E2021,
            linked_libs: vec![],
            linked_paths: vec![],
            cfgs: vec![],
            env: vec![],
            is_stdlib: false,
        }),
        dependencies: vec![
            dep_core.clone(),
            dep_std.clone(),
            dep_compiler_builtins.clone(),
            dep_crucible,
        ],
    });

    // Add byteorder
    custom_graph.push_unit_as_root(CustomUnit {
        target: CustomTarget::TargetLib(CustomTargetLib {
            crate_name: EXTRA_LIB_BYTEORDER.into(),
            src_path: [
                custom_sources_dir.as_path(),
                "byteorder".into(),
                "src".into(),
                "lib.rs".into(),
            ]
            .iter()
            .collect(),
            edition: Edition::E2021,
            linked_libs: vec![],
            linked_paths: vec![],
            cfgs: vec!["feature=\"std\"".into()],
            env: vec![],
            is_stdlib: false,
        }),
        dependencies: vec![dep_core, dep_std, dep_compiler_builtins],
    });

    // Create the necessary output directories.
    eprintln!("Setting up sysroot...");
    for subdir in ["bin", "etc", "lib", "libexec", "share"] {
        let new_dir = rlibs_sysroot.join(subdir);
        if generate_only {
            println!("mkdir -p {}", escape(new_dir.into_string().into()));
        } else {
            fs::create_dir_all(new_dir).unwrap_or_else(|err| {
                panic!(
                    "creating sysroot {} directory should succeed: {}",
                    subdir, err
                );
            });
        }
    }
    // Use relative symlink
    let rel_rlibs_dir = rlibs_dir
        .strip_prefix(out_dir)
        .expect("out_dir should be prefix of rlibs_dir");
    if generate_only {
        let rlibs_symlink = escape(rlibs_symlink.into_string().into());
        let rel_rlibs_dir = escape(rel_rlibs_dir.as_str().into());
        println!(
            "if [ ! -d {} ]; then ln -s {} {}; fi",
            rlibs_symlink, rel_rlibs_dir, rlibs_symlink
        );
    } else if !rlibs_symlink.is_dir() {
        unix::fs::symlink(rel_rlibs_dir, rlibs_symlink)
            .expect("creating rlibs symlink should succeed");
    }

    let mir_json_invocations =
        custom_graph
            .sequence_libs()
            .into_iter()
            .map(|lib| CmdInvocation {
                program: "mir-json".into(),
                args: {
                    let mut args = vec![
                        lib.target.src_path.into(),
                        "--edition".into(),
                        lib.target.edition.to_string(),
                        "--crate-name".into(),
                        lib.target.crate_name.into(),
                    ];
                    for cfg in lib.target.cfgs {
                        args.push("--cfg".into());
                        args.push(cfg);
                    }
                    for (extern_name, real_name) in lib.dependencies {
                        args.push("--extern".into());
                        args.push(format!(
                            "{}={}",
                            extern_name,
                            rlibs_dir.join(format!("lib{}.rlib", real_name))
                        ));
                    }
                    args.push("--target".into());
                    args.push(target_triple.into());
                    args.push("-L".into());
                    args.push(rlibs_dir.to_string());
                    args.push("--out-dir".into());
                    args.push(rlibs_dir.to_string());
                    args.push("--crate-type".into());
                    args.push("rlib".into());
                    args.push("--remap-path-prefix".into());
                    args.push(format!("{}=.", cwd));
                    // Stdlib crates need `-Z force-unstable-if-unmarked` to
                    // make stability attributes work properly.  But the extra
                    // libs must not be built with this flag, since the flag
                    // makes everything unstable by default, requiring users to
                    // use `#[feature(rustc_private)]`.
                    if lib.target.is_stdlib {
                        args.push("-Z".into());
                        args.push("force-unstable-if-unmarked".into());
                    }
                    // `-Z ub-checks` generates code that uses unsupported
                    // casts, such as pointer-to-integer casts in alignment
                    // checks.
                    args.push("-Z".into());
                    args.push("ub-checks=false".into());
                    for linked_path in lib.target.linked_paths {
                        args.push("-L".into());
                        args.push(linked_path.into());
                    }
                    for linked_lib in lib.target.linked_libs {
                        args.push("-l".into());
                        args.push(linked_lib.into());
                    }
                    args
                },
                env: lib.target.env,
            })
            // Special case: crucible_proc_macros is a proc-macro crate that we build with cargo
            // and copy into place.  This saves us from having to handle its syn/quote dependencies
            // ourselves.
            .chain([
                CmdInvocation {
                    program: "cargo".into(),
                    args: vec![
                        "build".into(),
                        "--release".into(),
                        "--manifest-path".into(),
                        custom_sources_dir.join(EXTRA_LIB_CRUCIBLE_PROC_MACROS)
                            .join("Cargo.toml").into(),
                    ],
                    env: vec![],
                },
                CmdInvocation {
                    program: "cp".into(),
                    args: vec![
                        custom_sources_dir.join(EXTRA_LIB_CRUCIBLE_PROC_MACROS)
                            .join("target").join("release")
                            .join(format!("lib{}", EXTRA_LIB_CRUCIBLE_PROC_MACROS))
                            .with_extension(PROC_MACRO_EXTENSION).into(),
                        rlibs_dir.to_string(),
                    ],
                    env: vec![],
                },
            ]);

    // Run mir-json.
    if generate_only {
        eprintln!("Generating translation steps...");
        for inv in mir_json_invocations {
            println!("{}", inv);
        }
    } else {
        for inv in mir_json_invocations {
            eprintln!("Executing: {}", inv);
            let status =
                inv.as_command().status().expect("mir-json should run");
            if !status.success() {
                panic!("mir-json exited with {}", status);
            }
        }
    }
}

/// Build a `cargo test -Z build-std` command.
fn cargo_test_cmd(project_dir: &TempDir, target_triple: &str) -> Command {
    let mut cmd = Command::new("cargo");
    cmd.current_dir(project_dir)
        .arg("test")
        .arg("--target")
        .arg(target_triple)
        .arg("-Z");
    // For some reason we need to explicitly include panic_abort on
    // wasm32-unknown-unknown.
    if target_triple == "wasm32-unknown-unknown" {
        cmd.arg("build-std=panic_abort,std");
    } else {
        cmd.arg("build-std");
    }
    cmd
}

/// `cp -r src dest`
fn copy_dir(src: &Utf8Path, dest: &Utf8Path) {
    let mut cp_cmd = Command::new("cp");
    cp_cmd.arg("-r").arg(src).arg(dest);
    let cp_status = cp_cmd.status().expect("cp should run");
    if !cp_status.success() {
        panic!("{:?} exited with {}", cp_cmd, cp_status);
    }
}
