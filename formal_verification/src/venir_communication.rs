use std::{
    io::Write,
    process::{Command, Stdio},
};

use fm::{FileId, FileManager, FileMap};
use nargo_cli::errors::CliError;
use noirc_errors::{
    CustomDiagnostic, DiagnosticKind, Location, Span, call_stack::CallStack,
    function_locations::FunctionLocations, reporter::ReportedErrors,
};
use serde::Deserialize;
use vir::ast::Krate;

use crate::payload::Outcome;
use crate::payload::counterexample::VenirModel;

/// The string Verus uses when a proof attempt exhausts its resource budget.
///
/// It arrives as an ordinary `SmtOutput::Error`, so this string is the only
/// thing distinguishing "the solver ran out of budget" from "the solver
/// rejected the program". From `air/src/main.rs` in the pinned `verus-lib`
/// revision, and mirrored in `scripts/run-corpus.py` and in CodeTracer's
/// `verification_report.nim`.
pub const RLIMIT_MARKER: &str = "Resource limit (rlimit) exceeded";

/// What one `venir` invocation established, structurally.
///
/// This exists so that the outcome reaches the payload emitter as a *value*
/// rather than being recovered from rendered text further up. `venir_verify`
/// used to return `Result<(), CliError>` and destroy every distinction on the
/// way out; the classification below is the same one the text tier has to
/// reconstruct by string matching, made once, at the place that actually knows.
pub struct VenirRun {
    /// Whether the `venir` process was started at all.
    pub solver_started: bool,
    /// Why it was not, when it was not.
    pub solver_unavailable_reason: Option<String>,
    pub outcome: Outcome,
    /// One line saying why, in the shape `run-corpus.py` writes into its report.
    pub detail: String,
    /// The diagnostics as `report_all` rendered them, kept rather than dropped.
    pub diagnostics: Vec<CustomDiagnostic>,
    /// The solver's counterexample model for each diagnostic, aligned index for
    /// index with [`VenirRun::diagnostics`]. `None` where there was none, which
    /// is every diagnostic that is not a failed proof and every failed proof
    /// from a `venir` that predates the model.
    ///
    /// Aligned rather than embedded because `diagnostics` is handed to
    /// `report_all` and to the outcome classifier as-is; the pairing is
    /// established before either runs and is asserted, so the two vectors cannot
    /// drift.
    pub models: Vec<Option<VenirModel>>,
    pub exit_code: Option<i32>,
    /// The terminal error the CLI must return, spelled exactly as it was
    /// before this type existed. Returning it from here rather than raising it
    /// lets the caller write a report first — a run that ends in an error is
    /// precisely the run whose report is worth having.
    pub failure: Option<String>,
    /// The arguments handed through to `venir`, for the oracle footprint.
    pub venir_args: Vec<String>,
}

/// Runs the Venir binary and passes the compiled program in VIR format to it
/// Reports all errors produced during Venir (SMT solver) verification
pub fn venir_verify(
    krate: Krate,
    workspace_file_manager: &FileManager,
    deny_warnings: bool,
    venir_args: &Vec<String>,
) -> Result<VenirRun, CliError> {
    let mut run = VenirRun {
        solver_started: false,
        solver_unavailable_reason: None,
        outcome: Outcome::PipelineError,
        detail: String::new(),
        diagnostics: Vec::new(),
        models: Vec::new(),
        exit_code: None,
        failure: None,
        venir_args: venir_args.clone(),
    };
    let serialized_vir_krate = serde_json::to_string(&krate).expect("Failed to serialize");

    // Run the Venir binary which is used for verifying the vir_krate input.
    let spawned = Command::new("venir")
        .args(venir_args.iter())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn();

    let mut child = match spawned {
        Ok(child) => child,
        Err(e) => {
            // Not a proof result. Nothing was established either way, and the
            // payload says exactly that rather than leaving the caller to
            // recognise this sentence.
            let message = format!(
                "Failed to start the Venir binary with the following error message\n{}\nTo fix this issue you can run the command nix develop",
                e
            );
            run.outcome = Outcome::NoSolver;
            run.detail = "Noir -> VIR pipeline completed; `venir` not available".to_string();
            run.solver_unavailable_reason = Some(format!("could not start `venir`: {e}"));
            run.failure = Some(message);
            return Ok(run);
        }
    };
    run.solver_started = true;

    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(serialized_vir_krate.as_bytes()).map_err(|e| {
            CliError::Generic(format!(
                "Failed to write to Venir stdin with the following error message\n{}",
                e.to_string()
            ))
        })?;
    }

    let output = child.wait_with_output().map_err(|e| {
        CliError::Generic(format!("Failed to read Venir stdout\n{}", e.to_string()))
    })?;

    let stdout_output = String::from_utf8_lossy(&output.stdout);
    if !stdout_output.is_empty() {
        println!("{}", stdout_output);
    }

    let stderr_output = String::from_utf8_lossy(&output.stderr);

    let has_crashed = !output.status.success();
    run.exit_code = output.status.code();

    let mut smt_outputs: Vec<SmtOutput> = Vec::new();
    let mut failed_deserialization_lines: Vec<&str> = Vec::new();

    for line in stderr_output.lines() {
        match serde_json::from_str::<SmtOutput>(line) {
            Ok(smt_output) => smt_outputs.push(smt_output),
            Err(_) => failed_deserialization_lines.push(line),
        }
    }

    if !failed_deserialization_lines.is_empty() {
        println!(
            "Failed to deserialize the following lines:\n{}",
            failed_deserialization_lines.join("\n")
        );
        run.detail = "`venir` wrote lines its own output standard does not describe".to_string();
        run.failure = Some("Failed to deserialize all lines outputted by Venir".to_string());
        return Ok(run);
    }

    let mut paired = pair_counterexamples_with_errors(smt_outputs);

    // Verus reports Notes in reverse order.
    paired.reverse();

    let mut verification_diagnostics: Vec<(CustomDiagnostic, Option<VenirModel>)> = paired
        .into_iter()
        .map(|(smt_output, model)| {
            (smt_output_to_diagnostic(smt_output, &workspace_file_manager), model)
        })
        .collect();

    // Sort errors by span. The model travels with its diagnostic.
    verification_diagnostics
        .sort_by_key(|(diag, _)| diag.secondaries.first().map(|label| label.location.span.start()));

    let (verification_diagnostics, models): (Vec<CustomDiagnostic>, Vec<Option<VenirModel>>) =
        verification_diagnostics.into_iter().unzip();
    assert_eq!(
        verification_diagnostics.len(),
        models.len(),
        "a model must accompany exactly one diagnostic"
    );

    // Report errors from the verification process.
    // `report_all` gained a `&FunctionLocations` argument since `beta.13`; it is used only
    // to name the frames of a runtime call stack when a diagnostic carries one. Verno's
    // diagnostics come from Venir/the SMT solver and never carry a Noir call stack, so an
    // empty map is the correct value rather than a placeholder.
    let function_locations = FunctionLocations::default();
    let reported_errors: ReportedErrors = noirc_errors::reporter::report_all(
        workspace_file_manager.as_file_map(),
        &function_locations,
        &verification_diagnostics,
        deny_warnings,
        false,
    );

    // The outcome, decided here, from values.
    //
    // Ordering mirrors `run-corpus.py::classify` for the case the two can both
    // see: a resource-limit exhaustion is recognised **before** anything is
    // allowed to count as a lost proof, because Verus serialises it as an
    // ordinary error block and it is one string away from a genuine rejection.
    let exhausted_budget = verification_diagnostics.iter().any(|diagnostic| {
        diagnostic.message.contains(RLIMIT_MARKER)
            || diagnostic.secondaries.iter().any(|label| label.message.contains(RLIMIT_MARKER))
    });

    run.diagnostics = verification_diagnostics;
    run.models = models;

    if has_crashed {
        // `venir` exited non-zero. The solver ran and failed to answer, which
        // none of the six outcomes names exactly; `pipeline-error` is the one
        // that does not claim anything about the program, which is the
        // property that matters. Note that the *text* tier classifies this as
        // `not-proved`, because `run-corpus.py::reached_solver` treats
        // "Verification crashed" as having reached the solver — the two tiers
        // disagree here, and the consumer's rule is to keep the text verdict
        // and refuse the payload rather than silently prefer either.
        run.outcome = Outcome::PipelineError;
        run.detail = "`venir` exited non-zero; the solver did not answer".to_string();
        run.failure = Some("Verification crashed!".to_string());
        return Ok(run);
    }

    if exhausted_budget {
        run.outcome = Outcome::TimedOut;
        run.detail = "solver rlimit exhausted".to_string();
        run.failure = Some(format!(
            "Verification failed due to {} previous errors!",
            reported_errors.error_count,
        ));
        return Ok(run);
    }

    if reported_errors.error_count > 0 {
        run.outcome = Outcome::NotProved;
        run.detail = run
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.kind == DiagnosticKind::Error)
            .map(|diagnostic| diagnostic.message.clone())
            .unwrap_or_else(|| "the solver did not discharge every obligation".to_string());
        run.failure = Some(format!(
            "Verification failed due to {} previous errors!",
            reported_errors.error_count,
        ));
        return Ok(run);
    }

    run.outcome = Outcome::Proved;
    run.detail = "verification successful".to_string();
    println!("Verification successful!");
    Ok(run)
}

/// Part of the Venir output standard.
#[derive(Deserialize)]
struct ErrorBlock {
    error_message: String,
    error_span: String,
    secondary_message: String,
}

/// Part of the Venir output standard.
#[derive(Deserialize)]
struct WarningBlock {
    warning_message: String,
}

/// Part of the Venir output standard.
#[derive(Deserialize)]
struct CrashBlock {
    crash_message: String,
    crash_span: String,
}

/// Part of the Venir output standard.
///
/// New in the revision of `venir` that stops discarding the solver's model. A
/// `venir` that predates it never writes this line and everything below simply
/// sees `None`; a `venir` that writes it against a Verno that did not know the
/// variant would have failed *every* run, because an unknown variant makes
/// `serde_json` reject the line and `venir_verify` treats an unparsed line as a
/// pipeline error. The two therefore move together, and that is deliberate:
/// silently ignoring an output shape is how a producer and a consumer drift.
#[derive(Deserialize)]
struct CounterexampleBlock {
    model: VenirModel,
}

/// The possible outputs of the Venir binary.
#[derive(Deserialize)]
enum SmtOutput {
    Error(ErrorBlock),
    Warning(WarningBlock),
    Note(String),
    AirMessage(CrashBlock),
    Counterexample(CounterexampleBlock),
}

/// Maps a Venir output to a Noir diagnostic type error.
fn smt_output_to_diagnostic(
    smt_output: SmtOutput,
    workspace_file_manager: &FileManager,
) -> CustomDiagnostic {
    let default_file_id = workspace_file_manager
        .as_file_map()
        .all_file_ids()
        .last()
        .cloned()
        .unwrap_or(FileId::dummy());

    match smt_output {
        SmtOutput::Error(error_block) => {
            let span = convert_span(&error_block.error_span);
            match span {
                Some((start_byte, final_byte, file_id)) => {
                    let file_id =
                        get_file_id_via_usize(workspace_file_manager.as_file_map(), file_id)
                            .unwrap_or(FileId::dummy());
                    CustomDiagnostic::simple_error(
                        error_block.error_message,
                        error_block.secondary_message,
                        Location::new(Span::inclusive(start_byte, final_byte), file_id),
                    )
                }
                None => CustomDiagnostic::from_message(&error_block.error_message, default_file_id),
            }
        }

        SmtOutput::Warning(warning_block) => CustomDiagnostic {
            file: default_file_id,
            message: warning_block.warning_message,
            secondaries: Vec::new(),
            notes: Vec::new(),
            kind: DiagnosticKind::Warning,
            deprecated: false,
            unnecessary: false,
            call_stack: CallStack::empty(),
        },

        SmtOutput::Note(message) => CustomDiagnostic {
            file: default_file_id,
            message,
            secondaries: Vec::new(),
            notes: Vec::new(),
            kind: DiagnosticKind::Info,
            deprecated: false,
            unnecessary: false,
            call_stack: CallStack::empty(),
        },

        // Handled before this function is reached: a counterexample is not a
        // diagnostic, it is evidence attached to one.
        SmtOutput::Counterexample(_) => {
            CustomDiagnostic::from_message("internal: unattached counterexample", default_file_id)
        }

        SmtOutput::AirMessage(crash_block) => {
            let span = convert_span(&crash_block.crash_span);
            match span {
                Some((start_byte, final_byte, file_id)) => {
                    let file_id =
                        get_file_id_via_usize(workspace_file_manager.as_file_map(), file_id)
                            .unwrap_or(default_file_id);
                    CustomDiagnostic::simple_error(
                        String::from("Verification crashed"),
                        crash_block.crash_message,
                        Location::new(Span::inclusive(start_byte, final_byte), file_id),
                    )
                }
                None => {
                    // No valid span for crash message; fallback to basic message
                    CustomDiagnostic::from_message(&crash_block.crash_message, default_file_id)
                }
            }
        }
    }
}

/// Attach each counterexample model to the message it explains.
///
/// `air` reports the model from inside `smt_get_model`, while the error it
/// belongs to is returned up to `rust_verify` and reported afterwards -- so on
/// the wire the model is the line **before** its error. That adjacency is the
/// only thing tying the two together when the query carried no assert-id, and
/// both the reversal and the span sort that follow would destroy it. So the
/// pairing is made here, once, on the order `venir` actually wrote.
///
/// Only an `Error` takes a model. A note or a warning between the two is
/// transparent rather than absorbing: it is not the thing the model explains,
/// and swallowing the model there would attach it to nothing.
fn pair_counterexamples_with_errors(
    smt_outputs: Vec<SmtOutput>,
) -> Vec<(SmtOutput, Option<VenirModel>)> {
    let mut paired: Vec<(SmtOutput, Option<VenirModel>)> = Vec::new();
    let mut pending_model: Option<VenirModel> = None;
    for smt_output in smt_outputs {
        match smt_output {
            SmtOutput::Counterexample(block) => {
                // Two models in a row would mean the first one's error never
                // arrived. Keep the newer one and say so, rather than attaching a
                // model to a message it does not describe.
                if pending_model.is_some() {
                    println!(
                        "`venir` reported two counterexample models with no error between them; \
                         the earlier one is dropped"
                    );
                }
                pending_model = Some(block.model);
            }
            other => {
                let model =
                    if matches!(other, SmtOutput::Error(_)) { pending_model.take() } else { None };
                paired.push((other, model));
            }
        }
    }
    if pending_model.is_some() {
        println!("`venir` reported a counterexample model with no error after it; it is dropped");
    }
    paired
}

/// Returns `FileId` for given id. `FileId` doesn't have a public constructor.
/// Therefore when we get the file id from the Venir error span we have to search
/// the file map and return the matching `FileId`.
fn get_file_id_via_usize(file_map: &FileMap, file_id_as_usize: usize) -> Option<FileId> {
    file_map.all_file_ids().find(|file_id| file_id.as_usize() == file_id_as_usize).cloned()
}

fn convert_span(input: &str) -> Option<(u32, u32, usize)> {
    if input.is_empty() {
        // Input is empty, cannot decode a span
        return None;
    }

    let trimmed = input.trim_matches(|c| c == '(' || c == ')');
    let parts: Vec<&str> = trimmed.split(',').map(str::trim).collect();

    if parts.len() != 3 {
        // Span must have exactly three components: start, end, file_id
        return None;
    }

    let start_byte = parts[0].parse::<u32>().ok()?;
    let final_byte = parts[1].parse::<u32>().ok()?;
    let file_id = parts[2].parse::<usize>().ok()?;

    Some((start_byte, final_byte, file_id))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::payload::counterexample::VenirBinding;

    /// Counted assertions, so a check that stopped asserting shows in the output.
    struct Counted {
        name: &'static str,
        n: usize,
    }

    impl Counted {
        fn new(name: &'static str) -> Counted {
            Counted { name, n: 0 }
        }
        fn eq<T: std::fmt::Debug + PartialEq>(&mut self, what: &str, actual: T, expected: T) {
            self.n += 1;
            assert_eq!(actual, expected, "[{}] {}", self.name, what);
        }
        fn done(self, expected: usize) {
            assert_eq!(
                self.n, expected,
                "[{}] made {} assertions, expected {}",
                self.name, self.n, expected
            );
            println!("[{}] {} assertions", self.name, self.n);
        }
    }

    fn model(tag: &str) -> VenirModel {
        VenirModel {
            parameters: vec![VenirBinding {
                variable: tag.to_string(),
                constant: tag.to_string(),
                value: "1".to_string(),
                typ: "Int".to_string(),
            }],
            ..VenirModel::default()
        }
    }

    fn cx(tag: &str) -> SmtOutput {
        SmtOutput::Counterexample(CounterexampleBlock { model: model(tag) })
    }

    fn error(message: &str) -> SmtOutput {
        SmtOutput::Error(ErrorBlock {
            error_message: message.to_string(),
            error_span: String::new(),
            secondary_message: String::new(),
        })
    }

    /// What the pairing produced, as `(message, model tag)`.
    fn pairs(outputs: Vec<SmtOutput>) -> Vec<(String, Option<String>)> {
        pair_counterexamples_with_errors(outputs)
            .into_iter()
            .map(|(out, model)| {
                let label = match &out {
                    SmtOutput::Error(e) => e.error_message.clone(),
                    SmtOutput::Warning(w) => w.warning_message.clone(),
                    SmtOutput::Note(n) => n.clone(),
                    SmtOutput::AirMessage(c) => c.crash_message.clone(),
                    SmtOutput::Counterexample(_) => "counterexample".to_string(),
                };
                (label, model.map(|m| m.parameters[0].variable.clone()))
            })
            .collect()
    }

    /// P1: a model belongs to the error that follows it, and is not itself a
    /// message. A model attached to the wrong error is worse than no model, so
    /// each of these arms names one way the attachment could go wrong.
    #[test]
    fn p1_a_model_attaches_to_the_error_that_follows_it() {
        let mut c = Counted::new("P1");

        c.eq(
            "the following error takes it",
            pairs(vec![cx("m0"), error("first")]),
            vec![("first".to_string(), Some("m0".to_string()))],
        );

        c.eq(
            "an error with no model before it takes none",
            pairs(vec![error("lonely")]),
            vec![("lonely".to_string(), None)],
        );

        c.eq(
            "only the first of two errors takes the one model",
            pairs(vec![cx("m0"), error("first"), error("second")]),
            vec![("first".to_string(), Some("m0".to_string())), ("second".to_string(), None)],
        );

        c.eq(
            "each model goes to its own error",
            pairs(vec![cx("m0"), error("first"), cx("m1"), error("second")]),
            vec![
                ("first".to_string(), Some("m0".to_string())),
                ("second".to_string(), Some("m1".to_string())),
            ],
        );

        c.done(4);
    }

    /// P2: notes and warnings are transparent, not absorbing.
    #[test]
    fn p2_a_note_between_a_model_and_its_error_does_not_absorb_it() {
        let mut c = Counted::new("P2");
        c.eq(
            "the note carries nothing and the error still gets the model",
            pairs(vec![cx("m0"), SmtOutput::Note("chosen trigger".to_string()), error("first")]),
            vec![
                ("chosen trigger".to_string(), None),
                ("first".to_string(), Some("m0".to_string())),
            ],
        );
        c.done(1);
    }

    /// P3: a model with nothing after it is dropped rather than attached
    /// backwards, and a counterexample never becomes a diagnostic of its own.
    #[test]
    fn p3_an_unattached_model_is_dropped() {
        let mut c = Counted::new("P3");
        c.eq(
            "a trailing model reaches no message",
            pairs(vec![error("first"), cx("m0")]),
            vec![("first".to_string(), None)],
        );
        c.eq("a model on its own produces no message at all", pairs(vec![cx("m0")]), Vec::new());
        c.eq(
            "two models in a row: the second wins, the first is dropped",
            pairs(vec![cx("m0"), cx("m1"), error("first")]),
            vec![("first".to_string(), Some("m1".to_string()))],
        );
        c.done(3);
    }
}
