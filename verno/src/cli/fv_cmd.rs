use clap::Args;
use formal_verification::{
    driver::compilation_pipeline::compile_and_build_vir_krate, venir_communication::venir_verify,
};
use nargo::{ops::report_errors, package::CrateName, prepare_package, workspace::Workspace};
use nargo_cli::{cli::compile_cmd::parse_workspace, errors::CliError};
use nargo_toml::PackageSelection;
use noirc_driver::{CompileOptions, link_to_debug_crate};
use noirc_frontend::debug::DebugInstrumenter;
use vir::ast::Krate;

use super::cli_components::{LockType, WorkspaceCommand};

/// Perform formal verification on a program
#[derive(Debug, Clone, Args)]
#[clap(visible_alias = "fv")]
pub struct FormalVerifyCommand {
    #[clap(flatten)]
    pub(super) package_options: PackageOptions,

    // This is necessary for compiling packages
    #[clap(flatten)]
    compile_options: CompileOptions,

    /// Emit debug information for the intermediate Verus VIR to stdout
    #[arg(long, hide = true)]
    pub show_vir: bool,

    // Flags which will be propagated to the Venir binary
    #[clap(last = true)]
    venir_flags: Vec<String>,
}

/// Options for commands that work on either workspace or package scope.
#[derive(Args, Clone, Debug, Default)]
pub struct PackageOptions {
    /// The name of the package to run the command on.
    /// By default run on the first one found moving up along the ancestors of the current directory.
    #[clap(long, conflicts_with = "workspace")]
    package: Option<CrateName>,

    /// Run on all packages in the workspace
    #[clap(long, conflicts_with = "package")]
    workspace: bool,
}

impl PackageOptions {
    /// Decide which package to run the command on:
    /// * `package` if non-empty
    /// * all packages if `workspace` is `true`
    /// * otherwise the default package
    pub fn package_selection(&self) -> PackageSelection {
        let default_selection =
            if self.workspace { PackageSelection::All } else { PackageSelection::DefaultOrAll };

        self.package.clone().map_or(default_selection, PackageSelection::Selected)
    }
}

impl WorkspaceCommand for FormalVerifyCommand {
    fn package_selection(&self) -> PackageSelection {
        self.package_options.package_selection()
    }

    fn lock_type(&self) -> LockType {
        LockType::Exclusive
    }
}

pub(crate) fn run(args: FormalVerifyCommand, workspace: Workspace) -> Result<(), CliError> {
    let (workspace_file_manager, parsed_files) = parse_workspace(&workspace, None);
    let binary_packages = workspace.into_iter().filter(|package| package.is_binary());

    for package in binary_packages {
        let (mut context, crate_id) =
            prepare_package(&workspace_file_manager, &parsed_files, package);
        link_to_debug_crate(&mut context, crate_id);
        context.debug_instrumenter = DebugInstrumenter::default();
        context.package_build_path = workspace.package_build_path(package);

        let krate: Krate = report_errors(
            compile_and_build_vir_krate(&mut context, crate_id, &args.compile_options),
            &workspace_file_manager,
            args.compile_options.deny_warnings,
            true,
        )?;

        // Shared post-processing
        if args.show_vir {
            println!("Generated VIR:");
            println!("{:#?}", krate);
        }

        venir_verify(
            krate,
            &workspace_file_manager,
            args.compile_options.deny_warnings,
            &args.venir_flags,
        )?;
    }

    Ok(())
}
