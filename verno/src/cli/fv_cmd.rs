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
    payload::{
        FindingKind, Outcome, Trust,
        emit::{
            PayloadBuilder, default_report_path, solver_invoked, solver_unavailable,
            venir_oracle_footprint,
        },
        panic_report,
    },
    venir_communication::{VenirRun, venir_verify},
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

    /// Where to write the structured verification report.
    ///
    /// Defaults to `<target-dir>/verno-report.json`, which is written on every
    /// run whether or not this flag is given. The default is a *convention*
    /// rather than an opt-in because the tool that consumes it cannot ask for
    /// it: CodeTracer runs the command a project declares in its own
    /// `tasks.json` and adds nothing to it (`Noir-Studio.md` §9.3).
    #[arg(long, value_name = "PATH")]
    pub report_json: Option<PathBuf>,

    /// Do not write the structured verification report.
    #[arg(long, conflicts_with = "report_json")]
    pub no_report_json: bool,

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

/// What a verification run established, before the report is written.
///
/// `failure` is the terminal `CliError` the command must still return, kept
/// separate so the report can be written first. A run that ends in an error is
/// precisely the run whose report is worth having.
struct RunSummary {
    outcome: Outcome,
    detail: String,
    solver_started: bool,
    solver_unavailable_reason: Option<String>,
    venir_args: Vec<String>,
    venir_exit_code: Option<i32>,
    failure: Option<String>,
}

impl RunSummary {
    fn pipeline_error(detail: impl Into<String>, failure: impl Into<String>) -> RunSummary {
        RunSummary {
            outcome: Outcome::PipelineError,
            detail: detail.into(),
            solver_started: false,
            solver_unavailable_reason: Some(
                "the run ended before the solver was started".to_string(),
            ),
            venir_args: Vec::new(),
            venir_exit_code: None,
            failure: Some(failure.into()),
        }
    }

    /// Fold one `venir` invocation into the run.
    ///
    /// The run's outcome is the **first** one that is not `proved`. Ranking
    /// them against each other would need an order nobody has agreed on — is a
    /// missing solver worse than an unproven obligation? — and "the first thing
    /// that was not a proof" is both defensible and reproducible.
    fn absorb(&mut self, run: &VenirRun) {
        if self.outcome == Outcome::Proved && run.outcome != Outcome::Proved {
            self.outcome = run.outcome;
            self.detail = run.detail.clone();
        }
        self.solver_started = self.solver_started || run.solver_started;
        if self.solver_unavailable_reason.is_none() {
            self.solver_unavailable_reason = run.solver_unavailable_reason.clone();
        }
        self.venir_args = run.venir_args.clone();
        self.venir_exit_code = run.exit_code.or(self.venir_exit_code);
        if self.failure.is_none() {
            self.failure = run.failure.clone();
        }
    }
}

pub(crate) fn run(args: FormalVerifyCommand, workspace: Workspace) -> Result<(), CliError> {
    let report_path: Option<PathBuf> = if args.no_report_json {
        None
    } else {
        Some(
            args.report_json
                .clone()
                .unwrap_or_else(|| default_report_path(&workspace.target_directory_path())),
        )
    };

    let argv: Vec<String> = std::env::args().collect();
    let mut builder = PayloadBuilder::new(&workspace.root_dir, argv.clone());
    let package_name = workspace
        .members
        .iter()
        .find(|package| package.is_binary())
        .map(|package| package.name.to_string());
    let entry_file = args.target_path.as_ref().map(|path| path.display().to_string());
    builder.set_package(package_name.clone());
    builder.set_entry_file(entry_file.clone());

    // Two of the six outcomes arrive as panics and unwind past every return
    // path here, so the hook is the only place that can write their report.
    if let Some(path) = &report_path {
        panic_report::arm(
            path.clone(),
            builder.started_at_unix_ms(),
            workspace.root_dir.display().to_string(),
            package_name,
            entry_file,
            argv,
        );
    }

    let (workspace_file_manager, parsed_files) = parse_workspace(&workspace, None);
    let summary = if let Some(target_path) = args.target_path.clone() {
        verify_functions_in_file(
            &args,
            &workspace,
            &workspace_file_manager,
            &parsed_files,
            target_path.as_path(),
            &mut builder,
        )
    } else {
        verify_workspace_binaries(
            &args,
            &workspace,
            &workspace_file_manager,
            &parsed_files,
            &mut builder,
        )
    };

    // The run reached a return path, so the hook must not fire on some later
    // panic and overwrite what we are about to write.
    panic_report::disarm();

    if let Some(path) = &report_path {
        let solver = if summary.solver_started {
            solver_invoked()
        } else {
            solver_unavailable(
                summary
                    .solver_unavailable_reason
                    .clone()
                    .unwrap_or_else(|| "no solver was started".to_string()),
            )
        };
        let oracle = if summary.solver_started {
            Some(venir_oracle_footprint(&summary.venir_args, summary.venir_exit_code))
        } else {
            None
        };
        let payload = builder.finish(summary.outcome, summary.detail.clone(), solver, oracle);
        if let Err(problem) = payload.write_to(path) {
            // Loud, and on stderr, but never fatal: a verification result the
            // developer can read is worth more than a report file, and
            // swallowing this would hide a producer bug from the one person
            // who could fix it.
            eprintln!("verno: could not write {}: {problem}", path.display());
        } else {
            println!("verno: wrote verification report to {}", path.display());
        }
    }

    match summary.failure {
        Some(message) => Err(CliError::Generic(message)),
        None => Ok(()),
    }
}

fn verify_workspace_binaries(
    args: &FormalVerifyCommand,
    workspace: &Workspace,
    workspace_file_manager: &fm::FileManager,
    parsed_files: &ParsedFiles,
    builder: &mut PayloadBuilder,
) -> RunSummary {
    let mut summary = RunSummary {
        outcome: Outcome::Proved,
        detail: "verification successful".to_string(),
        solver_started: false,
        solver_unavailable_reason: None,
        venir_args: Vec::new(),
        venir_exit_code: None,
        failure: None,
    };
    let mut verified_any = false;

    for package in workspace.members.iter().filter(|package| package.is_binary()) {
        let (mut context, crate_id) =
            prepare_package(workspace_file_manager, parsed_files, package);
        configure_context(&mut context, workspace, package, crate_id);

        let compiled = compile_and_build_vir_krate(&mut context, crate_id, &args.compile_options);
        record_compilation_errors(builder, workspace_file_manager, &compiled);

        let krate: Krate = match report_errors(
            compiled,
            workspace_file_manager,
            parsed_files,
            args.compile_options.deny_warnings,
            true,
        ) {
            Ok(krate) => krate,
            Err(error) => {
                return RunSummary::pipeline_error(
                    "the Noir front end rejected the program",
                    error.to_string(),
                );
            }
        };

        maybe_print_vir(args.show_vir, &krate);

        match venir_verify(
            krate,
            workspace_file_manager,
            args.compile_options.deny_warnings,
            &args.venir_flags,
        ) {
            Ok(run) => {
                record_venir_run(builder, workspace_file_manager, &run);
                summary.absorb(&run);
                if summary.failure.is_some() {
                    return summary;
                }
            }
            Err(error) => {
                return RunSummary::pipeline_error(
                    "the solver could not be driven to completion",
                    error.to_string(),
                );
            }
        }

        verified_any = true;
    }

    if verified_any {
        if summary.outcome == Outcome::Proved && builder.finding_count() == 0 {
            builder.add_finding(
                FindingKind::Proved,
                "Every proof obligation was discharged.",
                "",
                None,
                "Verification successful!",
                "a discharged obligation has nothing to mark",
                Trust::diagnostic_only(
                    "the per-finding record of a success; the run's own trust class carries \
                     the solver oracle footprint",
                ),
            );
        }
        summary
    } else {
        let message = "no binary packages with a `main` function were found; provide a Noir file path or point `--program-dir` at a binary crate".to_string();
        builder.add_finding(
            FindingKind::PipelineError,
            message.clone(),
            "",
            None,
            message.clone(),
            "the error is about the workspace, not about a line of Noir",
            Trust::diagnostic_only("the run reports on the workspace, not on a program"),
        );
        RunSummary::pipeline_error("no binary package to verify", message)
    }
}

/// Record the front end's diagnostics before `report_errors` consumes them.
///
/// `report_errors` prints and discards. Borrowing the error list first is the
/// whole of what is needed to keep the structure — the rendered text and the
/// payload then describe the same diagnostics rather than one being
/// reconstructed from the other.
fn record_compilation_errors(
    builder: &mut PayloadBuilder,
    workspace_file_manager: &fm::FileManager,
    compiled: &noirc_driver::CompilationResult<Krate>,
) {
    let Err(errors) = compiled else {
        return;
    };
    for diagnostic in errors {
        builder.add_diagnostic(
            workspace_file_manager,
            diagnostic,
            FindingKind::PipelineError,
            Trust::diagnostic_only(
                "a front-end error: Verno never reached the solver, so nothing was \
                 established about the program",
            ),
        );
    }
}

/// Record what `venir` said, as findings.
fn record_venir_run(
    builder: &mut PayloadBuilder,
    workspace_file_manager: &fm::FileManager,
    run: &VenirRun,
) {
    // The finding kind comes from the *outcome*, once, exactly as it does on
    // the consumer side. A run that exhausted its budget cannot contribute a
    // failed obligation even though its diagnostic is an `error:` block, and a
    // run that crashed cannot contribute one either.
    let kind = FindingKind::for_outcome(run.outcome);
    match run.outcome {
        Outcome::NoSolver => {
            builder.add_finding(
                kind,
                "The Noir to VIR pipeline completed; the solver was not started.",
                "Verno's solver back end (`venir`) is not available on this machine, so no \
                 proof was attempted. Nothing was established either way.",
                None,
                run.failure.clone().unwrap_or_default(),
                "no obligation was attempted, so there is nothing to point at",
                Trust::diagnostic_only("no solver ran; nothing was established either way"),
            );
        }
        Outcome::TimedOut => {
            builder.add_finding(
                kind,
                "The solver ran out of budget before it could answer.",
                "Not a failed proof: nothing was established either way. Re-run with a \
                 larger `--rlimit` to get an answer.",
                None,
                run.detail.clone(),
                "an exhausted budget is a property of the run, not of one line",
                Trust::diagnostic_only(
                    "the solver exhausted its resource limit; nothing was established",
                ),
            );
        }
        Outcome::Proved => {}
        _ => {
            for (index, diagnostic) in run.diagnostics.iter().enumerate() {
                if !diagnostic.is_error() {
                    continue;
                }
                let finding_id = builder.add_diagnostic(
                    workspace_file_manager,
                    diagnostic,
                    kind,
                    Trust::diagnostic_only(
                        "the solver did not discharge this obligation; with quantifiers and \
                         a resource limit that is not a proof the program is wrong",
                    ),
                );
                // The counterexample belongs to the obligation this diagnostic
                // reports, and only when the run is a failed proof: the wire
                // rules refuse a counterexample under any other outcome, because
                // a model of a query the solver never rejected would be evidence
                // for a claim nobody made.
                if run.outcome == Outcome::NotProved {
                    if let Some(Some(model)) = run.models.get(index) {
                        builder.add_counterexample(&finding_id, model);
                    }
                }
            }
        }
    }
}

fn verify_functions_in_file(
    args: &FormalVerifyCommand,
    workspace: &Workspace,
    workspace_file_manager: &fm::FileManager,
    parsed_files: &ParsedFiles,
    target_path: &Path,
    builder: &mut PayloadBuilder,
) -> RunSummary {
    let normalized_target = target_path.normalize();

    macro_rules! workspace_error {
        ($detail:expr, $message:expr) => {{
            let message: String = $message;
            builder.add_finding(
                FindingKind::PipelineError,
                message.clone(),
                "",
                None,
                message.clone(),
                "the error is about the invocation, not about a line of Noir",
                Trust::diagnostic_only("the run reports on the invocation, not on a program"),
            );
            return RunSummary::pipeline_error($detail, message);
        }};
    }

    if normalized_target.extension() != Some(OsStr::new(FILE_EXTENSION)) {
        workspace_error!(
            "the target is not a Noir source file",
            format!(
                "expected Noir source file with .{} extension, received `{}`",
                FILE_EXTENSION,
                normalized_target.display()
            )
        );
    }

    let Some(package) = find_enclosing_package(workspace, &normalized_target) else {
        workspace_error!(
            "the target is outside the workspace",
            format!(
                "`{}` does not belong to any package in the current workspace",
                normalized_target.display()
            )
        );
    };

    if workspace_file_manager.name_to_id(normalized_target.clone()).is_none() {
        workspace_error!(
            "the target is not part of the selected workspace",
            format!(
                "file `{}` is not part of the selected workspace; ensure it is included in the package",
                normalized_target.display()
            )
        );
    }

    let (mut context, crate_id) = prepare_package(workspace_file_manager, parsed_files, package);
    configure_context(&mut context, workspace, package, crate_id);

    let comp_result = check_crate(&mut context, crate_id, &args.compile_options);
    record_check_errors(builder, workspace_file_manager, &comp_result);

    if let Err(error) = report_errors(
        comp_result,
        workspace_file_manager,
        parsed_files,
        args.compile_options.deny_warnings,
        true,
    ) {
        return RunSummary::pipeline_error(
            "the Noir front end rejected the program",
            error.to_string(),
        );
    }

    let mut functions_to_verify =
        collect_functions_defined_in_file(&context, crate_id, &normalized_target);
    if functions_to_verify.is_empty() {
        workspace_error!(
            "the file declares nothing to verify",
            format!("no verifiable functions were found in `{}`", normalized_target.display())
        );
    }

    functions_to_verify.sort_by(|lhs, rhs| {
        function_sort_key(&context, lhs).cmp(&function_sort_key(&context, rhs))
    });

    let mut summary = RunSummary {
        outcome: Outcome::Proved,
        detail: "verification successful".to_string(),
        solver_started: false,
        solver_unavailable_reason: None,
        venir_args: Vec::new(),
        venir_exit_code: None,
        failure: None,
    };

    for func_id in functions_to_verify {
        let function_name = context.fully_qualified_function_name(&crate_id, &func_id);
        println!("Verifying `{function_name}`...");

        let compiled = compile_and_build_vir_for_entry_prechecked(
            &mut context,
            crate_id,
            func_id,
            &args.compile_options,
        );
        record_compilation_errors(builder, workspace_file_manager, &compiled);

        let krate: Krate = match report_errors(
            compiled,
            workspace_file_manager,
            parsed_files,
            args.compile_options.deny_warnings,
            true,
        ) {
            Ok(krate) => krate,
            Err(error) => {
                return RunSummary::pipeline_error(
                    "the Noir front end rejected the program",
                    error.to_string(),
                );
            }
        };

        maybe_print_vir(args.show_vir, &krate);

        match venir_verify(
            krate,
            workspace_file_manager,
            args.compile_options.deny_warnings,
            &args.venir_flags,
        ) {
            Ok(run) => {
                record_venir_run(builder, workspace_file_manager, &run);
                summary.absorb(&run);
                if summary.failure.is_some() {
                    return summary;
                }
            }
            Err(error) => {
                return RunSummary::pipeline_error(
                    "the solver could not be driven to completion",
                    error.to_string(),
                );
            }
        }
    }

    if summary.outcome == Outcome::Proved && builder.finding_count() == 0 {
        builder.add_finding(
            FindingKind::Proved,
            "Every proof obligation was discharged.",
            "",
            None,
            "Verification successful!",
            "a discharged obligation has nothing to mark",
            Trust::diagnostic_only(
                "the per-finding record of a success; the run's own trust class carries the \
                 solver oracle footprint",
            ),
        );
    }
    summary
}

/// The same capture as `record_compilation_errors`, for `check_crate`'s result.
fn record_check_errors<T>(
    builder: &mut PayloadBuilder,
    workspace_file_manager: &fm::FileManager,
    checked: &noirc_driver::CompilationResult<T>,
) {
    let Err(errors) = checked else {
        return;
    };
    for diagnostic in errors {
        builder.add_diagnostic(
            workspace_file_manager,
            diagnostic,
            FindingKind::PipelineError,
            Trust::diagnostic_only(
                "a front-end error: Verno never reached the solver, so nothing was \
                 established about the program",
            ),
        );
    }
}

fn configure_context(
    context: &mut Context,
    workspace: &Workspace,
    package: &Package,
    crate_id: CrateId,
) {
    let debug_path = Path::new("__debug").join("lib.nr");
    if context.file_manager.name_to_id(debug_path.clone()).is_some() {
        link_to_debug_crate(context, crate_id);
    }
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
                        // `Type::generic_count()` was removed upstream; `unwrap_forall` returns the
                        // same binder list a generic function's type is wrapped in, and an
                        // empty one for a non-generic function.
                        if !context
                            .def_interner
                            .function_meta(&func_id)
                            .typ
                            .unwrap_forall()
                            .0
                            .is_empty()
                        {
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
