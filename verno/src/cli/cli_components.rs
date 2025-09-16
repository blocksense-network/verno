use clap::Args;
use nargo::workspace::Workspace;
use nargo_cli::errors::CliError;
use nargo_toml::{
    ManifestError, PackageSelection, get_package_manifest, resolve_workspace_from_toml,
};
use std::{
    fs::File,
    path::{Path, PathBuf},
};

/// What kind of lock to take out on the (selected) workspace members.
#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)] // Not using `Shared` at the moment, e.g. while we `debug` we can `compile` a different version.
pub enum LockType {
    /// For commands that write artifacts.
    Exclusive,
    /// For commands that read artifacts, but never write them.
    Shared,
    /// For commands that cannot interfere with others.
    None,
}

/// Commands that can execute on the workspace level, or be limited to a selected package.
pub trait WorkspaceCommand {
    /// Indicate which package the command will be applied to.
    fn package_selection(&self) -> PackageSelection;
    /// The kind of lock the command needs to take out on the selected packages.
    fn lock_type(&self) -> LockType;
}

#[non_exhaustive]
#[derive(Args, Clone, Debug)]
pub struct NargoConfig {
    // REMINDER: Also change this flag in the LSP test lens if renamed
    #[arg(long, hide = true, global = true, default_value = "./", value_parser = parse_path)]
    program_dir: PathBuf,

    /// Override the default target directory.
    #[arg(long, hide = true, global = true, value_parser = parse_path)]
    target_dir: Option<PathBuf>,
}

/// Find the root directory, parse the workspace, lock the packages, then execute the command.
pub fn with_workspace<C, R>(cmd: C, config: NargoConfig, run: R) -> Result<(), CliError>
where
    C: WorkspaceCommand,
    R: FnOnce(C, Workspace) -> Result<(), CliError>,
{
    // All commands need to run on the workspace level, because that's where the `target` directory is.
    let workspace_dir = nargo_toml::find_root(&config.program_dir, true)?;
    let package_dir = nargo_toml::find_root(&config.program_dir, false)?;
    // Check if we're running inside the directory of a package, without having selected the entire workspace
    // or a specific package; if that's the case then parse the package name to select it in the workspace.
    let selection = match cmd.package_selection() {
        PackageSelection::DefaultOrAll if workspace_dir != package_dir => {
            let package = read_workspace(&package_dir, PackageSelection::DefaultOrAll)?;
            let package = package.into_iter().next().expect("there should be exactly 1 package");
            PackageSelection::Selected(package.name.clone())
        }
        other => other,
    };
    // Parse the top level workspace with the member selected.
    let mut workspace = read_workspace(&workspace_dir, selection)?;
    // Optionally override the target directory. It's only done here because most commands like the LSP and DAP
    // don't read or write artifacts, so they don't use the target directory.
    workspace.target_dir = config.target_dir.clone();
    // Lock manifests if the command needs it.
    let _locks = match cmd.lock_type() {
        LockType::None => None,
        typ => Some(lock_workspace(&workspace, typ == LockType::Exclusive)?),
    };
    run(cmd, workspace)
}

/// Parses a path and turns it into an absolute one by joining to the current directory.
fn parse_path(path: &str) -> Result<PathBuf, String> {
    use fm::NormalizePath;
    let mut path: PathBuf = path.parse().map_err(|e| format!("failed to parse path: {e}"))?;
    if !path.is_absolute() {
        path = std::env::current_dir().unwrap().join(path).normalize();
    }
    Ok(path)
}

/// Read a given program directory into a workspace.
fn read_workspace(
    program_dir: &Path,
    selection: PackageSelection,
) -> Result<Workspace, ManifestError> {
    let toml_path = get_package_manifest(program_dir)?;

    let workspace = resolve_workspace_from_toml(
        &toml_path, selection,
        // If we set the required env variables we could have an extra check for version compatibility.
        // For more information check file `tooling/nargo_cli/src/cli/mod.rs` in the Noir repo. (09.09.2025)
        None,
    )?;

    Ok(workspace)
}

/// Lock the (selected) packages in the workspace.
/// The lock taken can be shared for commands that only read the artifacts,
/// or exclusive for the ones that (might) write artifacts as well.
fn lock_workspace(
    workspace: &Workspace,
    exclusive: bool,
) -> Result<Vec<impl Drop + use<>>, CliError> {
    struct LockedFile(File);

    impl Drop for LockedFile {
        fn drop(&mut self) {
            let _ = fs2::FileExt::unlock(&self.0);
        }
    }

    let mut locks = Vec::new();
    for pkg in workspace.into_iter() {
        let toml_path = get_package_manifest(&pkg.root_dir)?;
        let path_display = toml_path.display();

        let file = File::open(&toml_path)
            .unwrap_or_else(|e| panic!("Expected {path_display} to exist: {e}"));

        if exclusive {
            if fs2::FileExt::try_lock_exclusive(&file).is_err() {
                eprintln!("Waiting for lock on {path_display}...");
            }
            fs2::FileExt::lock_exclusive(&file)
                .unwrap_or_else(|e| panic!("Failed to lock {path_display}: {e}"));
        } else {
            if fs2::FileExt::try_lock_shared(&file).is_err() {
                eprintln!("Waiting for lock on {path_display}...",);
            }
            fs2::FileExt::lock_shared(&file)
                .unwrap_or_else(|e| panic!("Failed to lock {path_display}: {e}"));
        }

        locks.push(LockedFile(file));
    }
    Ok(locks)
}
