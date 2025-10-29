use std::{
    collections::VecDeque,
    ffi::OsStr,
    path::{Path, PathBuf},
};

use clap::Args;
use fm::{FILE_EXTENSION, FileId, NormalizePath};
use formal_verification::{
    driver::compilation_pipeline::{
        compile_and_build_vir_for_entry_prechecked, compile_and_build_vir_krate,
    },
    venir_communication::venir_verify,
};
use nargo::{
    ops::report_errors,
    package::{CrateName, Package},
    prepare_package,
    workspace::Workspace,
};
use nargo_cli::{cli::compile_cmd::parse_workspace, errors::CliError};
use nargo_toml::PackageSelection;
use noirc_driver::{CompileOptions, check_crate, link_to_debug_crate};
use noirc_frontend::{
    debug::DebugInstrumenter,
    graph::CrateId,
    hir::{Context, ParsedFiles, def_map::ModuleDefId},
    node_interner::FuncId,
};
use vir::ast::Krate;

use super::cli_components::{LockType, WorkspaceCommand, parse_path};

/// Perform formal verification on a program
#[derive(Debug, Clone, Args)]
#[clap(visible_alias = "fv")]
pub struct FormalVerifyCommand {
    #[clap(flatten)]
    pub(super) package_options: PackageOptions,

    // This is necessary for compiling packages
    #[clap(flatten)]
    compile_options: CompileOptions,

    /// Verify every function defined in the provided Noir source file
    #[arg(
        value_name = "NOIR_FILE",
        help = "Path to a Noir source file whose functions should be verified (works for libraries without `main`). Use `--program-dir` or run inside the package so the file can be resolved.",
        value_parser = parse_path
    )]
    target_path: Option<PathBuf>,

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
    if let Some(target_path) = args.target_path.clone() {
        verify_functions_in_file(
            &args,
            &workspace,
            &workspace_file_manager,
            &parsed_files,
            target_path.as_path(),
        )
    } else {
        verify_workspace_binaries(&args, &workspace, &workspace_file_manager, &parsed_files)
    }
}

fn verify_workspace_binaries(
    args: &FormalVerifyCommand,
    workspace: &Workspace,
    workspace_file_manager: &fm::FileManager,
    parsed_files: &ParsedFiles,
) -> Result<(), CliError> {
    let mut verified_any = false;

    for package in workspace.members.iter().filter(|package| package.is_binary()) {
        let (mut context, crate_id) =
            prepare_package(workspace_file_manager, parsed_files, package);
        configure_context(&mut context, workspace, package, crate_id);

        let krate: Krate = report_errors(
            compile_and_build_vir_krate(&mut context, crate_id, &args.compile_options),
            workspace_file_manager,
            args.compile_options.deny_warnings,
            true,
        )?;

        maybe_print_vir(args.show_vir, &krate);

        venir_verify(
            krate,
            workspace_file_manager,
            args.compile_options.deny_warnings,
            &args.venir_flags,
        )?;

        verified_any = true;
    }

    if verified_any {
        Ok(())
    } else {
        Err(CliError::Generic(
            "no binary packages with a `main` function were found; provide a Noir file path or point `--program-dir` at a binary crate".to_string(),
        ))
    }
}

fn verify_functions_in_file(
    args: &FormalVerifyCommand,
    workspace: &Workspace,
    workspace_file_manager: &fm::FileManager,
    parsed_files: &ParsedFiles,
    target_path: &Path,
) -> Result<(), CliError> {
    let normalized_target = target_path.normalize();

    if normalized_target.extension() != Some(OsStr::new(FILE_EXTENSION)) {
        return Err(CliError::Generic(format!(
            "expected Noir source file with .{} extension, received `{}`",
            FILE_EXTENSION,
            normalized_target.display()
        )));
    }

    let package = find_enclosing_package(workspace, &normalized_target).ok_or_else(|| {
        CliError::Generic(format!(
            "`{}` does not belong to any package in the current workspace",
            normalized_target.display()
        ))
    })?;

    let _ = workspace_file_manager.name_to_id(normalized_target.clone()).ok_or_else(|| {
        CliError::Generic(format!(
            "file `{}` is not part of the selected workspace; ensure it is included in the package",
            normalized_target.display()
        ))
    })?;

    let (mut context, crate_id) = prepare_package(workspace_file_manager, parsed_files, package);
    configure_context(&mut context, workspace, package, crate_id);

    let comp_result = check_crate(&mut context, crate_id, &args.compile_options);

    report_errors(comp_result, workspace_file_manager, args.compile_options.deny_warnings, true)?;

    let mut functions_to_verify =
        collect_functions_defined_in_file(&context, crate_id, &normalized_target);
    if functions_to_verify.is_empty() {
        return Err(CliError::Generic(format!(
            "no verifiable functions were found in `{}`",
            normalized_target.display()
        )));
    }

    functions_to_verify.sort_by(|lhs, rhs| {
        function_sort_key(&context, lhs).cmp(&function_sort_key(&context, rhs))
    });

    for func_id in functions_to_verify {
        let function_name = context.fully_qualified_function_name(&crate_id, &func_id);
        println!("Verifying `{function_name}`...");

        let krate: Krate = report_errors(
            compile_and_build_vir_for_entry_prechecked(
                &mut context,
                crate_id,
                func_id,
                &args.compile_options,
            ),
            workspace_file_manager,
            args.compile_options.deny_warnings,
            true,
        )?;

        maybe_print_vir(args.show_vir, &krate);

        venir_verify(
            krate,
            workspace_file_manager,
            args.compile_options.deny_warnings,
            &args.venir_flags,
        )?;
    }

    Ok(())
}

fn configure_context(
    context: &mut Context,
    workspace: &Workspace,
    package: &Package,
    crate_id: CrateId,
) {
    link_to_debug_crate(context, crate_id);
    context.debug_instrumenter = DebugInstrumenter::default();
    context.package_build_path = workspace.package_build_path(package);
}

fn maybe_print_vir(show_vir: bool, krate: &Krate) {
    if show_vir {
        println!("Generated VIR:");
        println!("{:#?}", krate);
    }
}

fn function_sort_key(context: &Context, func_id: &FuncId) -> (FileId, u32, String) {
    let location = context.def_interner.function_meta(func_id).name.location;
    let span = location.span;
    (location.file, span.start(), context.def_interner.function_name(func_id).to_string())
}

fn collect_functions_defined_in_file(
    context: &Context,
    crate_id: CrateId,
    target_path: &Path,
) -> Vec<FuncId> {
    let normalized_target = target_path.normalize();

    let Some(def_map) = context.def_map(&crate_id) else {
        return Vec::new();
    };

    let mut func_ids_from_file: Vec<FuncId> = Vec::new();
    let mut queue_modules =
        VecDeque::from_iter(def_map.modules().iter().map(|(_, module_data)| module_data));

    while let Some(value) = queue_modules.pop_front() {
        for module_def_id in value.value_definitions() {
            match module_def_id {
                ModuleDefId::ModuleId(module_id) => {
                    // Also iterate over all functions in child modules
                    queue_modules.push_back(module_id.module(&context.def_maps))
                }
                ModuleDefId::FunctionId(func_id) => {
                    let meta = context.def_interner.function_meta(&func_id);
                    if context
                        .file_manager
                        .path(meta.name.location.file)
                        .map(|path| path.normalize() == normalized_target)
                        .unwrap_or(false)
                    {
                        if context.def_interner.function_meta(&func_id).typ.generic_count() > 0 {
                            let function_name =
                                context.fully_qualified_function_name(&crate_id, &func_id);
                            println!("Skipping `{function_name}` because it's generic...");
                        } else {
                            assert!(
                                !func_ids_from_file.contains(&func_id),
                                "The func_id {} was encountered twice which shouldn't be possible",
                                func_id
                            );
                            func_ids_from_file.push(func_id);
                        }
                    }
                }
                _ => (),
            }
        }
    }

    func_ids_from_file
}

fn find_enclosing_package<'a>(workspace: &'a Workspace, target: &Path) -> Option<&'a Package> {
    workspace
        .members
        .iter()
        .filter(|package| target.starts_with(package.root_dir.normalize()))
        .max_by_key(|package| package.root_dir.components().count())
}
