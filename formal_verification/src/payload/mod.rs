//! VN-M4 — the structured verification payload Verno emits for CodeTracer.
//!
//! # What this is
//!
//! One verification run produces one JSON document, written to
//! `<target-dir>/verno-report.json`. The document is the *whole* of what Verno
//! has to say about the run in machine-readable form: which of the six outcomes
//! it reached, the findings with their Noir source ranges, and — when a solver
//! ever supplies one — a counterexample, a proof-goal tree and the solver query
//! behind them.
//!
//! The consumer side is specified in
//! `codetracer-specs/Planned-Features/SMT-Counterexample-And-Prover-State-Visualization.md`.
//! **That document owns the payload names**; this module is an emitter for them,
//! not a second schema. The five names it lists — `SolverCounterexampleTrace`,
//! `ProofGoalTree`, `ProverStateFrame`, `SolverQueryAttachment` and
//! `ProofVisualizationSourceMap` — appear here as
//! [`SolverCounterexampleTrace`], [`ProofGoalTree`], [`ProverStateFrame`],
//! [`SolverQueryAttachment`] and [`ProofVisualizationSourceMap`], and the
//! envelope that carries them is [`VerificationPayload`].
//!
//! # Three rules this module exists to enforce
//!
//! **1. The six outcomes survive.** [`Outcome`] has exactly the six values
//! `scripts/run-corpus.py` names, spelled identically. A payload that could only
//! say "proved" or "not proved" would collapse the distinction this project
//! exists to protect. One of the six — a wall-clock timeout — can never appear
//! in a payload at all, because the producer is killed before it can write one;
//! see [`Outcome::TimedOut`].
//!
//! **2. Nothing is ever silently empty.** Verno's solver back end used to
//! return five strings per diagnostic and no model at all. It now returns the
//! solver's own model as well -- `air` stopped discarding the `(get-model)`
//! response it had already parsed, and `venir` writes it as a `Counterexample`
//! line; see [`counterexample`] and `venir_communication.rs`. What it still does
//! not return is a proof-goal structure or any SMT text, and a `venir` older
//! than that change returns no model either. So a slot Verno cannot fill is
//! present and *explicitly* empty: [`ModelStatus`] is a required field and
//! `Unavailable` carries a required reason. An empty binding list without a
//! status would read as "the solver found no relevant variables", which is a
//! different and false claim.
//!
//! **3. Every payload carries its trust class.** [`TrustClass`] has the four
//! values the visualization spec lists, and it is a required field on the
//! envelope and on every finding, counterexample, goal tree and query
//! attachment. There is no default. A consumer that receives a payload without
//! one must reject it rather than assume a level — see the CodeTracer-side
//! decoder, which does exactly that.
//!
//! # What Verno can honestly fill today
//!
//! The envelope, the findings with their Noir spans, the source map, and — since
//! VN-M5 — the counterexample body: the solver's values, the program points it
//! passed through in the order it reached them, and the obligation it violates.
//! Not the goal tree and not the SMT query text; neither exists at the `venir`
//! boundary. Not a source position for a program point either: the
//! snapshot-to-span map (`SnapPos`) is built inside `vir`/`rust_verify` and does
//! not cross. Where the contract has a slot Verno cannot fill, the slot is
//! present and empty with a stated reason rather than omitted, so a consumer can
//! tell "this producer does not have it" from "this run did not produce it".

use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

pub mod counterexample;
pub mod emit;
pub mod panic_report;

/// The schema identifier every payload carries.
///
/// A consumer that does not recognise this exact string must refuse the
/// document rather than guess at its shape. The version is part of the string
/// so that a producer and a consumer can never agree on the name while
/// disagreeing on the fields.
pub const SCHEMA_ID: &str = "codetracer.verification/v1";

/// The file name Verno writes inside the package's target directory.
///
/// This is a convention rather than a flag because CodeTracer cannot add a flag:
/// `Noir-Studio.md` §9.3 has the IDE surface the actions a project declares and
/// "invent no manifest of our own", so the IDE runs the project's own
/// `tasks.json` command verbatim. A payload only reaches CodeTracer if Verno
/// writes it without being asked.
pub const REPORT_FILE_NAME: &str = "verno-report.json";

// ---------------------------------------------------------------------------
// Outcome
// ---------------------------------------------------------------------------

/// The six ways a Verno run can end.
///
/// Spelled exactly as `scripts/run-corpus.py` spells them, and exactly as
/// CodeTracer's `viewmodels/verification_report.nim` spells them, so the three
/// vocabularies compare without a translation table.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Outcome {
    /// Every obligation discharged. The only outcome that is positive evidence
    /// about the program.
    #[serde(rename = "proved")]
    Proved,
    /// The solver ran and rejected an obligation. **The only one of the six
    /// that is a failed proof.**
    #[serde(rename = "not-proved")]
    NotProved,
    /// The solver ran out of budget. Says nothing about the program.
    ///
    /// A payload can only ever carry this for a *solver resource limit*
    /// (`rlimit`), which `venir` reports as an ordinary error. A **wall-clock**
    /// timeout kills Verno before it can write anything, so that case produces
    /// no payload at all and stays with the consumer's text-tier classifier.
    /// This is the one place where the contract cannot carry an outcome, and it
    /// is stated rather than papered over.
    #[serde(rename = "timed-out")]
    TimedOut,
    /// Verno does not implement a construct the program uses. Says nothing
    /// about the program. Never a failed proof.
    #[serde(rename = "unsupported")]
    Unsupported,
    /// The Noir → VIR pipeline completed and the solver was never started.
    /// The normal outcome on macOS, where `venir` is unavailable.
    #[serde(rename = "no-solver")]
    NoSolver,
    /// Verno failed before the solver. Includes `unreachable!()`, which is a
    /// bug in Verno and is deliberately *not* folded into `Unsupported`.
    #[serde(rename = "pipeline-error")]
    PipelineError,
}

impl Outcome {
    /// Whether the run said anything at all about whether the program is
    /// correct. Two of six do; the other four are reports about the *tool*.
    pub fn answers_correctness(self) -> bool {
        matches!(self, Outcome::Proved | Outcome::NotProved)
    }

    /// The single definition of "the verifier rejected this program".
    pub fn is_failed_proof(self) -> bool {
        self == Outcome::NotProved
    }

    /// The wire spelling, for messages and tests.
    pub fn as_str(self) -> &'static str {
        match self {
            Outcome::Proved => "proved",
            Outcome::NotProved => "not-proved",
            Outcome::TimedOut => "timed-out",
            Outcome::Unsupported => "unsupported",
            Outcome::NoSolver => "no-solver",
            Outcome::PipelineError => "pipeline-error",
        }
    }
}

// ---------------------------------------------------------------------------
// Trust
// ---------------------------------------------------------------------------

/// How much weight the data below may be given.
///
/// The four values are the ones
/// `SMT-Counterexample-And-Prover-State-Visualization.md` lists under "The
/// payload must record whether the displayed data is". They line up with
/// GRIP's `EvidenceDispositionIR` (`kernel_checked`, `externally_checked`,
/// `solver_oracle_trusted`, `diagnostic_only`), minus its `rejected`, which is
/// a disposition of an *attempt* rather than a class of displayed data.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TrustClass {
    /// Checked by a trusted core. **Verno never emits this.** There is no
    /// kernel in this pipeline; nothing here is checked by anything.
    #[serde(rename = "checked-by-trusted-core")]
    CheckedByTrustedCore,
    /// A solver result that was independently reconstructed into a proof.
    /// **Verno never emits this.** `venir` returns no proof object.
    #[serde(rename = "proof-reconstructed")]
    ProofReconstructed,
    /// Accepted because a solver said so, on an explicit oracle footprint.
    /// This is what a Verno `proved` is: Z3 answered `unsat` through Verus and
    /// nothing checked it.
    #[serde(rename = "solver-oracle")]
    SolverOracle,
    /// Shown to a developer, and not evidence of anything. Every Verno finding
    /// that is not a `proved` verdict is this, **including a failed
    /// obligation**: in a logic with quantifiers and a resource limit, "the
    /// solver did not discharge this" is not a proof that the program is
    /// wrong.
    #[serde(rename = "diagnostic-only")]
    DiagnosticOnly,
}

/// A trust class with the reason it was chosen.
///
/// The reason is required, not decorative. A trust class with no stated basis
/// is the thing this field exists to prevent: it would let a producer label a
/// diagnostic `solver-oracle` and have no one able to see that it never ran a
/// solver.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Trust {
    pub class: TrustClass,
    pub reason: String,
    /// Present only for [`TrustClass::SolverOracle`]: what was trusted, and
    /// what could not be recorded about it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub oracle_footprint: Option<OracleFootprint>,
}

impl Trust {
    pub fn diagnostic_only(reason: impl Into<String>) -> Trust {
        Trust { class: TrustClass::DiagnosticOnly, reason: reason.into(), oracle_footprint: None }
    }

    pub fn solver_oracle(reason: impl Into<String>, footprint: OracleFootprint) -> Trust {
        Trust {
            class: TrustClass::SolverOracle,
            reason: reason.into(),
            oracle_footprint: Some(footprint),
        }
    }
}

/// What a `solver-oracle` claim rests on.
///
/// Every optional field here is one Verno cannot fill today, and each one says
/// why in `*_absent_reason`. `venir` prints only diagnostics on its structured
/// channel: it computes `time_smt_init`, `time_smt_run` and `rlimit_count` per
/// bucket and never reports them, and it never names the SMT solver or its
/// version. A footprint that quietly omitted those would claim a more complete
/// audit trail than exists.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OracleFootprint {
    /// The program Verno actually executed. `"venir"`, resolved on `PATH`.
    pub tool: String,
    /// The arguments Verno passed through to it (`verno fv -- --rlimit 10`).
    pub tool_args: Vec<String>,
    /// The exit status, when the process ran to completion.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub exit_code: Option<i32>,
    /// The SMT solver behind `venir`, when it names itself. It does not today.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver: Option<String>,
    /// Why [`Self::solver`] is absent. Required whenever it is `None`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_absent_reason: Option<String>,
    /// Query counts and timings, when the back end reports them. It does not
    /// today.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub statistics: Option<BTreeMap<String, String>>,
    /// Why [`Self::statistics`] is absent. Required whenever it is `None`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub statistics_absent_reason: Option<String>,
}

// ---------------------------------------------------------------------------
// Source locations
// ---------------------------------------------------------------------------

/// A range in a Noir source file.
///
/// Lines and columns are 1-based, matching what `noirc_errors::reporter` prints
/// and what CodeTracer's `SourceRange` means. Byte offsets are carried
/// alongside because they are what Verno actually has — `noirc_errors::Span` is
/// a byte range — and converting to line/column loses information a consumer
/// may want back.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceLocation {
    /// Path as the reporter renders it, relative to the package where possible.
    pub file: String,
    /// Index into [`ProofVisualizationSourceMap::files`], so a consumer can
    /// resolve the file without re-deriving the path.
    pub file_index: usize,
    pub start_line: u32,
    pub start_column: u32,
    pub end_line: u32,
    pub end_column: u32,
    pub byte_start: u32,
    pub byte_end: u32,
}

/// The mapping from payload nodes back to source, per the spec's
/// `ProofVisualizationSourceMap`.
///
/// Verno's mapping is one level deep: Noir source ranges only. There is no
/// generated-code layer to map through, because the VIR Verno builds is
/// consumed in-process and never shown. The `generated_origin` slot on
/// [`ProverStateFrame`] is where that would go.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofVisualizationSourceMap {
    /// Every file any location in this payload refers to, indexed by
    /// [`SourceLocation::file_index`].
    pub files: Vec<SourceFile>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceFile {
    pub index: usize,
    /// Path as printed in diagnostics.
    pub path: String,
    /// Absolute path, when Verno resolved one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub absolute_path: Option<String>,
}

// ---------------------------------------------------------------------------
// Findings
// ---------------------------------------------------------------------------

/// What one line of a report *is*.
///
/// Mirrors CodeTracer's `VerificationFindingKind` one-for-one. These are not
/// severities: a limitation and a failed obligation can both stop you shipping,
/// and they demand opposite reactions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FindingKind {
    #[serde(rename = "proved")]
    Proved,
    /// The solver could not discharge an obligation. The only kind that is
    /// evidence about the program.
    #[serde(rename = "failed-obligation")]
    FailedObligation,
    /// Verno does not implement a construct the program uses.
    #[serde(rename = "limitation")]
    Limitation,
    #[serde(rename = "budget-exhausted")]
    BudgetExhausted,
    #[serde(rename = "solver-unavailable")]
    SolverUnavailable,
    #[serde(rename = "pipeline-error")]
    PipelineError,
}

impl FindingKind {
    /// The kind a given outcome produces. Decided once, here, from the outcome
    /// — the same discipline `buildReport` follows on the CodeTracer side, and
    /// for the same reason: it makes it impossible for an `unsupported` run to
    /// contribute a failed obligation even when its output also contains an
    /// `error:` block.
    pub fn for_outcome(outcome: Outcome) -> FindingKind {
        match outcome {
            Outcome::Proved => FindingKind::Proved,
            Outcome::NotProved => FindingKind::FailedObligation,
            Outcome::TimedOut => FindingKind::BudgetExhausted,
            Outcome::Unsupported => FindingKind::Limitation,
            Outcome::NoSolver => FindingKind::SolverUnavailable,
            Outcome::PipelineError => FindingKind::PipelineError,
        }
    }
}

/// One thing the verifier said.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Finding {
    /// Stable within one payload. Counterexamples and goal trees refer to a
    /// finding by this id rather than by index, so reordering cannot silently
    /// re-point them.
    pub id: String,
    pub kind: FindingKind,
    /// The verifier's own headline, verbatim.
    pub message: String,
    /// The secondary label ("failed postcondition"), verbatim, or empty.
    #[serde(default)]
    pub detail: String,
    /// For [`FindingKind::Limitation`] only: the construct Verno named after
    /// its `UNSUPPORTED:` prefix.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub construct: Option<String>,
    /// `None` when the finding has no Noir source position.
    ///
    /// This is genuinely common and must not be faked: Verno's `todo!()` panics
    /// carry a *Rust* position (`expr_to_vir/types.rs:56:13`), never a Noir
    /// one. A marker on line 1 is a claim about code that made no such claim.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Why [`Self::location`] is absent. Required whenever it is `None`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location_absent_reason: Option<String>,
    /// The rendered diagnostic block, as the reporter printed it. This is the
    /// text tier's content, carried inside the structured payload so the two
    /// tiers cannot disagree about what the verifier said.
    #[serde(default)]
    pub excerpt: String,
    pub trust: Trust,
}

// ---------------------------------------------------------------------------
// Counterexamples
// ---------------------------------------------------------------------------

/// Whether the model is there, and if not, why not.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModelStatus {
    /// Every variable relevant to the violated obligation has a value.
    #[serde(rename = "complete")]
    Complete,
    /// Some values are present; others were not recoverable. A consumer must
    /// not present a partial model as a full execution.
    #[serde(rename = "partial")]
    Partial,
    /// No values at all.
    #[serde(rename = "unavailable")]
    Unavailable,
}

/// One variable's value in the solver's model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModelBinding {
    /// The Noir source name. Verno preserves this into the query:
    /// `vir::ast::VarIdent(name, VarIdentDisambiguate::RustcId(local_id))` is
    /// built from the Noir identifier and its `LocalId`.
    pub name: String,
    /// The Noir `LocalId`, when the variable came from one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub local_id: Option<u32>,
    /// The value as the solver gave it, rendered.
    pub value: String,
    /// The Noir type, when known.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_name: Option<String>,
    /// Where the variable is declared. Available for parameters (Verno keeps
    /// per-parameter `Location`s in `param_source.rs`); absent for locals until
    /// a `VarIdent -> Location` side-table exists.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

/// The model, or its stated absence. Never an unexplained empty list.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleModel {
    pub status: ModelStatus,
    /// Required whenever `status` is not [`ModelStatus::Complete`].
    #[serde(skip_serializing_if = "Option::is_none")]
    pub absent_reason: Option<String>,
    #[serde(default)]
    pub bindings: Vec<ModelBinding>,
}

impl CounterexampleModel {
    pub fn unavailable(reason: impl Into<String>) -> CounterexampleModel {
        CounterexampleModel {
            status: ModelStatus::Unavailable,
            absent_reason: Some(reason.into()),
            bindings: Vec::new(),
        }
    }
}

/// What one step of a counterexample trace is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StepKind {
    #[serde(rename = "assumption")]
    Assumption,
    #[serde(rename = "assignment")]
    Assignment,
    /// A branch the model forced. `taken` says which way.
    #[serde(rename = "branch")]
    Branch,
    /// One iteration of a bounded unrolling.
    #[serde(rename = "loop-iteration")]
    LoopIteration,
    #[serde(rename = "call")]
    Call,
    /// The first assertion, contract, invariant or postcondition the model
    /// violates. At most one step in a trace has this kind.
    #[serde(rename = "violation")]
    Violation,
}

/// One point on the failing path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CounterexampleStep {
    pub index: usize,
    pub kind: StepKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    pub description: String,
    /// Values that became known at this step.
    #[serde(default)]
    pub bindings: Vec<ModelBinding>,
    /// For [`StepKind::Branch`]: whether the model took the branch.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub taken: Option<bool>,
    /// For [`StepKind::LoopIteration`]: which iteration of the unrolling.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub iteration: Option<u32>,
    /// The path condition active here, rendered.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path_condition: Option<String>,
}

/// What kind of source-level obligation the model violates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObligationKind {
    #[serde(rename = "precondition")]
    Precondition,
    #[serde(rename = "postcondition")]
    Postcondition,
    #[serde(rename = "assertion")]
    Assertion,
    #[serde(rename = "loop-invariant")]
    LoopInvariant,
    #[serde(rename = "loop-decreases")]
    LoopDecreases,
    #[serde(rename = "arithmetic-overflow")]
    ArithmeticOverflow,
    /// The verifier named something this enum does not cover. The raw text is
    /// in [`ViolatedObligation::raw_kind`]; inventing a category would be worse
    /// than saying "other".
    #[serde(rename = "other")]
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ViolatedObligation {
    pub kind: ObligationKind,
    /// The verifier's own wording, always, whether or not `kind` is `Other`.
    pub raw_kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    pub message: String,
}

/// The spec's `SolverCounterexampleTrace`: replayable trace data for one model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverCounterexampleTrace {
    pub id: String,
    /// The [`Finding::id`] this counterexample belongs to.
    pub finding_id: String,
    pub trust: Trust,
    pub model: CounterexampleModel,
    #[serde(default)]
    pub steps: Vec<CounterexampleStep>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub violated_obligation: Option<ViolatedObligation>,
    /// The [`SolverQueryAttachment::id`] this came from.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_query_id: Option<String>,
    /// **Always `false`.** Serialised anyway, and required on the wire, because
    /// the spec's rule — "When no real execution exists, the counterexample
    /// trace remains a visual diagnostic artifact and must not be presented as
    /// recorded runtime evidence" — is easier to enforce against a field that
    /// must be present and false than against a field that is merely absent.
    pub is_recorded_execution: bool,
}

// ---------------------------------------------------------------------------
// Proof goal trees
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofNodeKind {
    #[serde(rename = "source-obligation")]
    SourceObligation,
    #[serde(rename = "tactic-step")]
    TacticStep,
    #[serde(rename = "subgoal")]
    Subgoal,
    #[serde(rename = "smt-query")]
    SmtQuery,
    #[serde(rename = "solver-result")]
    SolverResult,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Hypothesis {
    pub name: String,
    pub statement: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
}

/// The spec's `ProverStateFrame`: one node in the proof tree.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProverStateFrame {
    /// Stable across regenerations of the same artifact, so a consumer can
    /// preserve which nodes the user had expanded. This is the spec's
    /// `SolverViz.GeneratedOriginStable` requirement.
    pub id: String,
    pub kind: ProofNodeKind,
    pub goal: String,
    #[serde(default)]
    pub hypotheses: Vec<Hypothesis>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<SourceLocation>,
    /// Path through generated code, when the goal came from a lowering rather
    /// than from source. Verno's lowering passes (`loop_unroll`, `mut_args`,
    /// `tuple_deconstruction`) synthesise nodes with no source counterpart;
    /// this is where they would identify themselves.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generated_origin: Option<String>,
    /// What produced this state.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub produced_by: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub solver_query_id: Option<String>,
    #[serde(default)]
    pub children: Vec<ProverStateFrame>,
}

/// The spec's `ProofGoalTree`: a proof-state tree rooted at one source
/// obligation.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProofGoalTree {
    pub id: String,
    pub finding_id: String,
    pub trust: Trust,
    pub root: ProverStateFrame,
}

// ---------------------------------------------------------------------------
// Solver queries
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReplayStatus {
    #[serde(rename = "not-attempted")]
    NotAttempted,
    #[serde(rename = "reproduced")]
    Reproduced,
    #[serde(rename = "diverged")]
    Diverged,
}

/// The spec's `SolverQueryAttachment`.
///
/// Every content field is optional with a required `*_absent_reason`, because
/// Verno can fill none of them: `venir` does not return the SMT-LIB text, the
/// model, the unsat core or the statistics, and Verno never sees the solver
/// process at all.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverQueryAttachment {
    pub id: String,
    pub trust: Trust,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub smtlib: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub smtlib_absent_reason: Option<String>,
    #[serde(default)]
    pub options: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rlimit: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model: Option<CounterexampleModel>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unsat_core: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unsat_core_absent_reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub statistics: Option<BTreeMap<String, String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub statistics_absent_reason: Option<String>,
    pub replay_status: ReplayStatus,
}

// ---------------------------------------------------------------------------
// The envelope
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Producer {
    pub name: String,
    pub version: String,
    /// The language the payload is about.
    pub source_language: String,
    /// Which release of that language's toolchain the producer is built
    /// against. `check-noir-pin.sh` guarantees this is a single upstream tag.
    pub language_release: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolverInfo {
    /// Whether a solver process was started at all.
    pub invoked: bool,
    pub name: String,
    /// Required whenever `invoked` is false.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unavailable_reason: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RunInfo {
    /// Wall-clock start, milliseconds since the epoch.
    ///
    /// A consumer uses this to reject a *stale* payload: a report left behind
    /// by a previous run would otherwise be read as this run's result, which is
    /// the most dangerous failure mode this contract has — it would show a
    /// developer a counterexample for code they have since fixed.
    pub started_at_unix_ms: u64,
    pub finished_at_unix_ms: u64,
    pub workspace_root: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub package: Option<String>,
    /// The single file, when the run was `verno fv <file>` rather than a whole
    /// package.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub entry_file: Option<String>,
    pub argv: Vec<String>,
    pub solver: SolverInfo,
}

/// One verification run, in full.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerificationPayload {
    /// Must equal [`SCHEMA_ID`].
    pub schema: String,
    pub producer: Producer,
    pub run: RunInfo,
    pub outcome: Outcome,
    /// One line saying why, in the shape `run-corpus.py` writes into its report.
    pub outcome_detail: String,
    /// The trust class of the run's *verdict*.
    pub trust: Trust,
    pub findings: Vec<Finding>,
    #[serde(default)]
    pub counterexample_traces: Vec<SolverCounterexampleTrace>,
    #[serde(default)]
    pub goal_trees: Vec<ProofGoalTree>,
    #[serde(default)]
    pub solver_queries: Vec<SolverQueryAttachment>,
    #[serde(default)]
    pub source_map: ProofVisualizationSourceMap,
}

/// A rule the payload broke.
///
/// The producer checks its own output before writing it. That is not
/// belt-and-braces: these are exactly the invariants the consumer will reject
/// the document for, so catching them here turns a silent degradation to the
/// text tier into a Verno bug report.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractViolation(pub String);

impl std::fmt::Display for ContractViolation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl VerificationPayload {
    /// Every rule the contract states, checked.
    ///
    /// Kept as one function returning *all* violations rather than the first,
    /// so a producer change that breaks three rules is not fixed one round-trip
    /// at a time.
    pub fn check(&self) -> Vec<ContractViolation> {
        let mut problems = Vec::new();
        let mut fail = |message: String| problems.push(ContractViolation(message));

        if self.schema != SCHEMA_ID {
            fail(format!("schema is `{}`, expected `{}`", self.schema, SCHEMA_ID));
        }

        // A limitation is not a proof result. This is VN-M3's central property,
        // restated as a wire rule so that it cannot be lost in translation.
        for finding in &self.findings {
            if finding.kind == FindingKind::Limitation && self.outcome.answers_correctness() {
                fail(format!(
                    "finding `{}` is a limitation but the run outcome `{}` claims to answer \
                     correctness; a limitation says nothing about the program",
                    finding.id,
                    self.outcome.as_str()
                ));
            }
            if finding.kind == FindingKind::FailedObligation && self.outcome != Outcome::NotProved {
                fail(format!(
                    "finding `{}` is a failed obligation but the run outcome is `{}`; only \
                     `not-proved` may carry one",
                    finding.id,
                    self.outcome.as_str()
                ));
            }
            if finding.location.is_none() && finding.location_absent_reason.is_none() {
                fail(format!(
                    "finding `{}` has no location and no `location_absent_reason`",
                    finding.id
                ));
            }
            if finding.kind == FindingKind::Limitation && finding.construct.is_none() {
                fail(format!(
                    "finding `{}` is a limitation but does not name the construct",
                    finding.id
                ));
            }
            check_trust(&finding.trust, &format!("finding `{}`", finding.id), &mut fail);
        }

        let ids: Vec<&str> = self.findings.iter().map(|f| f.id.as_str()).collect();
        for (index, id) in ids.iter().enumerate() {
            if ids[..index].contains(id) {
                fail(format!("duplicate finding id `{id}`"));
            }
        }

        // A counterexample is a model of a *rejected* obligation. Attaching one
        // to any other outcome would let a timeout or an unsupported construct
        // present as a disproof.
        for trace in &self.counterexample_traces {
            if self.outcome != Outcome::NotProved {
                fail(format!(
                    "counterexample `{}` is present but the run outcome is `{}`; only \
                     `not-proved` may carry one",
                    trace.id,
                    self.outcome.as_str()
                ));
            }
            if !ids.contains(&trace.finding_id.as_str()) {
                fail(format!(
                    "counterexample `{}` refers to unknown finding `{}`",
                    trace.id, trace.finding_id
                ));
            }
            if trace.is_recorded_execution {
                fail(format!(
                    "counterexample `{}` claims to be a recorded execution; a solver model \
                     is never one",
                    trace.id
                ));
            }
            if trace.model.status != ModelStatus::Complete && trace.model.absent_reason.is_none() {
                fail(format!(
                    "counterexample `{}` has a non-complete model and no `absent_reason`",
                    trace.id
                ));
            }
            if trace.model.status == ModelStatus::Unavailable && !trace.model.bindings.is_empty() {
                fail(format!(
                    "counterexample `{}` says its model is unavailable but carries bindings",
                    trace.id
                ));
            }
            if trace.trust.class != TrustClass::DiagnosticOnly {
                fail(format!(
                    "counterexample `{}` is `{:?}`; a solver model is diagnostic-only",
                    trace.id, trace.trust.class
                ));
            }
            let violations =
                trace.steps.iter().filter(|step| step.kind == StepKind::Violation).count();
            if violations > 1 {
                fail(format!(
                    "counterexample `{}` marks {violations} steps as the violation; \
                     at most one may be",
                    trace.id
                ));
            }
            check_trust(&trace.trust, &format!("counterexample `{}`", trace.id), &mut fail);
        }

        for tree in &self.goal_trees {
            if !ids.contains(&tree.finding_id.as_str()) {
                fail(format!(
                    "goal tree `{}` refers to unknown finding `{}`",
                    tree.id, tree.finding_id
                ));
            }
            check_trust(&tree.trust, &format!("goal tree `{}`", tree.id), &mut fail);
        }

        for query in &self.solver_queries {
            if query.smtlib.is_none() && query.smtlib_absent_reason.is_none() {
                fail(format!(
                    "solver query `{}` has no SMT-LIB text and no `smtlib_absent_reason`",
                    query.id
                ));
            }
            check_trust(&query.trust, &format!("solver query `{}`", query.id), &mut fail);
        }

        // A `solver-oracle` claim without a footprint is the exact thing the
        // trust field exists to make impossible.
        check_trust(&self.trust, "run", &mut fail);
        if self.outcome == Outcome::Proved && self.trust.class != TrustClass::SolverOracle {
            fail(format!(
                "outcome is `proved` but the run trust class is `{:?}`; a discharged \
                 obligation rests on the solver oracle and must say so",
                self.trust.class
            ));
        }
        if self.trust.class == TrustClass::SolverOracle && !self.run.solver.invoked {
            fail("run trust class is `solver-oracle` but no solver was invoked".to_string());
        }
        if !self.run.solver.invoked && self.run.solver.unavailable_reason.is_none() {
            fail("no solver was invoked and no `unavailable_reason` is given".to_string());
        }

        // Every location must resolve through the source map, or a consumer
        // cannot open the file the payload points at.
        let file_count = self.source_map.files.len();
        for finding in &self.findings {
            if let Some(location) = &finding.location {
                if location.file_index >= file_count {
                    fail(format!(
                        "finding `{}` points at source-map file {} of {}",
                        finding.id, location.file_index, file_count
                    ));
                }
            }
        }

        problems
    }

    /// Serialise, having checked. Refuses to produce a document that breaks its
    /// own contract.
    pub fn to_json(&self) -> Result<String, ContractViolation> {
        let problems = self.check();
        if !problems.is_empty() {
            let joined: Vec<String> = problems.iter().map(|p| p.0.clone()).collect();
            return Err(ContractViolation(joined.join("; ")));
        }
        serde_json::to_string_pretty(self)
            .map_err(|error| ContractViolation(format!("serialisation failed: {error}")))
    }

    /// Write the payload to `path`, creating parent directories.
    ///
    /// Written to a sibling temporary file and renamed, so a consumer polling
    /// the path can never read half a document. The rename is within one
    /// directory, so it is atomic on every platform Verno runs on.
    pub fn write_to(&self, path: &Path) -> Result<(), io::Error> {
        let json =
            self.to_json().map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error.0))?;
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        let temporary = temporary_sibling(path);
        std::fs::write(&temporary, json.as_bytes())?;
        std::fs::rename(&temporary, path)
    }
}

fn temporary_sibling(path: &Path) -> PathBuf {
    let mut name = path.file_name().unwrap_or_default().to_os_string();
    name.push(format!(".{}.tmp", std::process::id()));
    path.with_file_name(name)
}

fn check_trust(trust: &Trust, subject: &str, fail: &mut impl FnMut(String)) {
    if trust.reason.trim().is_empty() {
        fail(format!("{subject} states a trust class with no reason"));
    }
    if trust.class == TrustClass::SolverOracle && trust.oracle_footprint.is_none() {
        fail(format!("{subject} claims `solver-oracle` trust with no oracle footprint"));
    }
    if trust.class != TrustClass::SolverOracle && trust.oracle_footprint.is_some() {
        fail(format!("{subject} carries an oracle footprint but is not `solver-oracle`"));
    }
    if let Some(footprint) = &trust.oracle_footprint {
        if footprint.solver.is_none() && footprint.solver_absent_reason.is_none() {
            fail(format!("{subject}'s oracle footprint names no solver and gives no reason"));
        }
        if footprint.statistics.is_none() && footprint.statistics_absent_reason.is_none() {
            fail(format!("{subject}'s oracle footprint has no statistics and gives no reason"));
        }
    }
}

#[cfg(test)]
mod conformance_tests;

#[cfg(test)]
mod counterexample_tests;

#[cfg(test)]
mod tests;
