//! Building a [`VerificationPayload`](super::VerificationPayload) out of what
//! Verno actually has.
//!
//! Two things happen here that are worth stating plainly.
//!
//! **Verno does not classify itself by scraping its own text.** The consumer's
//! text tier has to, because text is all it has; a producer that did the same
//! would inherit every fragility the structured payload exists to remove. So
//! [`PayloadBuilder::finish`] takes the outcome as an argument, and the call
//! sites pass the outcome they *know* they are in: the spawn failure, the
//! panic, the compile error, the solver's verdict.
//!
//! **Line and column are computed the way `codespan_reporting` computes them**
//! — a character count from the start of the line, one-based — so the payload's
//! numbers and the numbers in the rendered diagnostic are the same numbers. If
//! they drifted, a consumer that merged the two tiers would put a marker one
//! column away from the text it quotes.

use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use fm::{FileId, FileManager};
use noirc_errors::{CustomDiagnostic, Location};

use super::counterexample::{ObligationInfo, VenirModel, trace_from_model};
use super::{
    ContractViolation, Finding, FindingKind, OracleFootprint, Outcome, Producer,
    ProofVisualizationSourceMap, REPORT_FILE_NAME, RunInfo, SCHEMA_ID, SolverCounterexampleTrace,
    SolverInfo, SourceFile, SourceLocation, Trust, VerificationPayload,
};

/// The Noir release Verno is built against.
///
/// Pinned here as well as in `Cargo.toml` so the payload can state it without a
/// build script. The two are kept in agreement by a test in this crate, not by
/// hope — see `tests::the_noir_release_constant_matches_the_pin`.
pub const NOIR_RELEASE: &str = "v1.0.0-beta.26";

/// What a counterexample says it is a counterexample *to*, read off the finding.
///
/// Taken from the finding rather than passed in beside it, so the violation the
/// trace marks and the diagnostic the developer reads cannot end up pointing at
/// different places. The secondary label is preferred over the headline because
/// that is the one that names the obligation ("assertion failed") rather than
/// the function it was in.
pub fn obligation_from(finding: &Finding) -> ObligationInfo {
    ObligationInfo {
        message: if finding.detail.is_empty() {
            finding.message.clone()
        } else {
            finding.detail.clone()
        },
        location: finding.location.clone(),
    }
}

/// Milliseconds since the Unix epoch, or 0 if the clock is before it.
pub fn now_unix_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|elapsed| elapsed.as_millis() as u64)
        .unwrap_or(0)
}

/// Where Verno writes its report when nothing overrides it.
///
/// `<target-dir>/verno-report.json`. The consumer looks in the same place
/// relative to the project root it launched the action in, so neither side has
/// to parse the other's output to find the file.
pub fn default_report_path(target_directory: &Path) -> PathBuf {
    target_directory.join(REPORT_FILE_NAME)
}

/// Accumulates a payload across a run.
pub struct PayloadBuilder {
    started_at_unix_ms: u64,
    workspace_root: String,
    package: Option<String>,
    entry_file: Option<String>,
    argv: Vec<String>,
    files: Vec<SourceFile>,
    file_ids: Vec<usize>,
    findings: Vec<Finding>,
    next_finding: usize,
    counterexample_traces: Vec<SolverCounterexampleTrace>,
}

impl PayloadBuilder {
    pub fn new(workspace_root: &Path, argv: Vec<String>) -> PayloadBuilder {
        PayloadBuilder {
            started_at_unix_ms: now_unix_ms(),
            workspace_root: workspace_root.display().to_string(),
            package: None,
            entry_file: None,
            argv,
            files: Vec::new(),
            file_ids: Vec::new(),
            findings: Vec::new(),
            next_finding: 0,
            counterexample_traces: Vec::new(),
        }
    }

    pub fn started_at_unix_ms(&self) -> u64 {
        self.started_at_unix_ms
    }

    pub fn set_package(&mut self, package: Option<String>) {
        self.package = package;
    }

    pub fn set_entry_file(&mut self, entry: Option<String>) {
        self.entry_file = entry;
    }

    fn allocate_id(&mut self) -> String {
        let id = format!("f{}", self.next_finding);
        self.next_finding += 1;
        id
    }

    /// Register a file in the source map and return its index.
    fn file_index(&mut self, file_manager: &FileManager, file_id: FileId) -> usize {
        let raw = file_id.as_usize();
        if let Some(position) = self.file_ids.iter().position(|known| *known == raw) {
            return position;
        }
        let file_map = file_manager.as_file_map();
        let path = file_map
            .get_name(file_id)
            .map(|name| name.to_string())
            .unwrap_or_else(|_| format!("<file {raw}>"));
        let absolute = file_map.get_absolute_name(file_id).map(|name| name.to_string()).ok();
        let index = self.files.len();
        self.files.push(SourceFile { index, path, absolute_path: absolute });
        self.file_ids.push(raw);
        index
    }

    /// Turn a Noir byte span into a payload location.
    ///
    /// Returns `None` when the span points at a file the manager does not have,
    /// which is what a dummy `FileId` looks like. A location we cannot resolve
    /// is reported as absent, never as line 1.
    pub fn location_for(
        &mut self,
        file_manager: &FileManager,
        location: Location,
    ) -> Option<SourceLocation> {
        let file_map = file_manager.as_file_map();
        let source = file_map.get_file(location.file)?.source().to_string();
        let byte_start = location.span.start();
        let byte_end = location.span.end();
        let (start_line, start_column) = line_and_column(&source, byte_start as usize);
        let (end_line, end_column) = line_and_column(&source, byte_end as usize);
        let index = self.file_index(file_manager, location.file);
        Some(SourceLocation {
            file: self.files[index].path.clone(),
            file_index: index,
            start_line,
            start_column,
            end_line,
            end_column,
            byte_start,
            byte_end,
        })
    }

    /// Add a finding built from a Noir diagnostic.
    ///
    /// `kind` is passed in rather than derived from the diagnostic's severity,
    /// because severity does not determine kind: a solver error and a
    /// type error are both `error:` blocks and mean entirely different things.
    /// The caller knows which phase it is in; the diagnostic does not.
    pub fn add_diagnostic(
        &mut self,
        file_manager: &FileManager,
        diagnostic: &CustomDiagnostic,
        kind: FindingKind,
        trust: Trust,
    ) -> String {
        // codespan renders the header location from the first non-dummy label,
        // so that is the location this finding claims. Using any other one
        // would put the payload and the printed text on different lines.
        let primary = diagnostic.secondaries.iter().find(|label| !label.location.is_dummy());
        let location = primary.and_then(|label| self.location_for(file_manager, label.location));
        let detail = primary.map(|label| label.message.clone()).unwrap_or_default();
        let id = self.allocate_id();
        let excerpt = render_excerpt(diagnostic, location.as_ref());
        self.findings.push(Finding {
            id: id.clone(),
            kind,
            message: diagnostic.message.clone(),
            detail,
            construct: None,
            location_absent_reason: if location.is_none() {
                Some(
                    "the diagnostic carried no resolvable Noir source span; \
                     pointing at an arbitrary line would be a claim the verifier did not make"
                        .to_string(),
                )
            } else {
                None
            },
            location,
            excerpt,
            trust,
        });
        id
    }

    /// Add a finding that has no diagnostic behind it — a limitation, an absent
    /// solver, an exhausted budget.
    pub fn add_finding(
        &mut self,
        kind: FindingKind,
        message: impl Into<String>,
        detail: impl Into<String>,
        construct: Option<String>,
        excerpt: impl Into<String>,
        location_absent_reason: impl Into<String>,
        trust: Trust,
    ) -> String {
        let id = self.allocate_id();
        self.findings.push(Finding {
            id: id.clone(),
            kind,
            message: message.into(),
            detail: detail.into(),
            construct,
            location: None,
            location_absent_reason: Some(location_absent_reason.into()),
            excerpt: excerpt.into(),
            trust,
        });
        id
    }

    pub fn finding_count(&self) -> usize {
        self.findings.len()
    }

    pub fn counterexample_count(&self) -> usize {
        self.counterexample_traces.len()
    }

    /// Attach the solver's counterexample to a finding already added.
    ///
    /// Returns the trace's id, or `None` when the model carried no values -- a
    /// trace with no bindings and no steps would satisfy every wire rule and
    /// then be offered to a developer as an execution to walk through. The
    /// obligation's location is taken from the finding rather than passed in
    /// separately, so the marked violation and the rendered diagnostic point at
    /// the same place by construction.
    pub fn add_counterexample(&mut self, finding_id: &str, model: &VenirModel) -> Option<String> {
        let finding = self.findings.iter().find(|f| f.id == finding_id)?;
        let obligation = obligation_from(finding);
        let id = format!("cx{}", self.counterexample_traces.len());
        let trace = trace_from_model(id.clone(), finding_id, model, obligation)?;
        self.counterexample_traces.push(trace);
        Some(id)
    }

    /// Close the payload.
    ///
    /// `solver` says whether a solver process was started; the run trust class
    /// is derived from that and from the outcome rather than passed in, so a
    /// caller cannot label a run `solver-oracle` by mistake.
    pub fn finish(
        self,
        outcome: Outcome,
        outcome_detail: impl Into<String>,
        solver: SolverInfo,
        oracle: Option<OracleFootprint>,
    ) -> VerificationPayload {
        let trust = match (outcome, oracle) {
            (Outcome::Proved, Some(footprint)) => Trust::solver_oracle(
                "every obligation was discharged by the SMT solver behind `venir`; \
                 nothing re-checked its answer",
                footprint,
            ),
            (Outcome::Proved, None) => Trust::diagnostic_only(
                "the run reported success but no solver footprint was recorded, so the \
                 result cannot be presented as solver-backed evidence",
            ),
            (Outcome::NotProved, _) => Trust::diagnostic_only(
                "the solver did not discharge an obligation; with quantifiers and a \
                 resource limit that is not a proof the program is wrong",
            ),
            _ => Trust::diagnostic_only(
                "the run reports on the verifier rather than on the program; nothing was \
                 established either way",
            ),
        };

        VerificationPayload {
            schema: SCHEMA_ID.to_string(),
            producer: Producer {
                name: "verno".to_string(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                source_language: "noir".to_string(),
                language_release: NOIR_RELEASE.to_string(),
            },
            run: RunInfo {
                started_at_unix_ms: self.started_at_unix_ms,
                finished_at_unix_ms: now_unix_ms(),
                workspace_root: self.workspace_root,
                package: self.package,
                entry_file: self.entry_file,
                argv: self.argv,
                solver,
            },
            outcome,
            outcome_detail: outcome_detail.into(),
            trust,
            findings: self.findings,
            counterexample_traces: self.counterexample_traces,
            // Still nothing to put here, and the reason is still `venir`. It
            // carries the solver's model now; it carries no proof-goal structure
            // and no SMT text at all -- `air` computes `time_smt_init`,
            // `time_smt_run` and `rlimit_count` per bucket and prints none of
            // them, and the unsat core is only requested under a feature Venir
            // does not enable. Empty rather than filled with plausible-looking
            // data.
            goal_trees: Vec::new(),
            solver_queries: Vec::new(),
            source_map: ProofVisualizationSourceMap { files: self.files },
        }
    }
}

/// The footprint Verno can honestly record for a `venir` run.
///
/// Everything it cannot record says why. This is not defensive padding: an
/// oracle footprint whose missing fields were simply omitted would claim a more
/// complete audit trail than exists, and the whole point of the trust class is
/// that a reader can see what it rests on.
pub fn venir_oracle_footprint(args: &[String], exit_code: Option<i32>) -> OracleFootprint {
    OracleFootprint {
        tool: "venir".to_string(),
        tool_args: args.to_vec(),
        exit_code,
        solver: None,
        solver_absent_reason: Some(
            "`venir` does not name the SMT solver or its version on any output channel".to_string(),
        ),
        statistics: None,
        statistics_absent_reason: Some(
            "`venir` computes per-bucket `time_smt_init`, `time_smt_run` and `rlimit_count` \
             and reports none of them"
                .to_string(),
        ),
    }
}

/// A one-line reason for a solver that was never started.
pub fn solver_unavailable(reason: impl Into<String>) -> SolverInfo {
    SolverInfo {
        invoked: false,
        name: "venir".to_string(),
        unavailable_reason: Some(reason.into()),
    }
}

pub fn solver_invoked() -> SolverInfo {
    SolverInfo { invoked: true, name: "venir".to_string(), unavailable_reason: None }
}

/// Write a payload, reporting a contract violation as an error rather than
/// silently producing nothing.
pub fn write_payload(payload: &VerificationPayload, path: &Path) -> Result<(), ContractViolation> {
    payload
        .write_to(path)
        .map_err(|error| ContractViolation(format!("could not write {}: {error}", path.display())))
}

// ---------------------------------------------------------------------------
// Line and column
// ---------------------------------------------------------------------------

/// One-based line and column for a byte offset.
///
/// The column is a **character** count from the start of the line, which is
/// what `codespan_reporting` prints (`files::column_index` counts char
/// boundaries in `line_range.start .. byte_index`). A byte count would differ
/// on any line containing a non-ASCII character, and Noir source may.
pub fn line_and_column(source: &str, byte_index: usize) -> (u32, u32) {
    let clamped = byte_index.min(source.len());
    let mut line = 1u32;
    let mut line_start = 0usize;
    for (offset, character) in source.char_indices() {
        if offset >= clamped {
            break;
        }
        if character == '\n' {
            line += 1;
            line_start = offset + 1;
        }
    }
    let column = source[line_start..clamped].chars().count() as u32 + 1;
    (line, column)
}

/// The diagnostic as text, in the shape the text tier already knows.
///
/// Deliberately *not* a re-implementation of codespan's renderer. It is a
/// compact restatement — headline, location, secondary label, notes — because
/// the payload's job is to carry the structure, and the consumer already has
/// the rendered block from the process output when it wants the full picture.
fn render_excerpt(diagnostic: &CustomDiagnostic, location: Option<&SourceLocation>) -> String {
    let mut lines = vec![format!("error: {}", diagnostic.message)];
    if let Some(location) = location {
        lines.push(format!(
            "  ┌─ {}:{}:{}",
            location.file, location.start_line, location.start_column
        ));
    }
    for label in &diagnostic.secondaries {
        if !label.message.is_empty() {
            lines.push(format!("  = {}", label.message));
        }
    }
    for note in &diagnostic.notes {
        if !note.is_empty() {
            lines.push(format!("  = {note}"));
        }
    }
    lines.join("\n")
}
