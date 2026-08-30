//! Turning `venir`'s counterexample model into the payload's
//! [`SolverCounterexampleTrace`](super::SolverCounterexampleTrace).
//!
//! **This is new ground for the campaign.** Every earlier milestone recorded
//! that `venir` returns no model. That was true, and the reason was not `venir`:
//! `air`'s `smt_get_model` parsed the whole of the solver's `(get-model)`
//! response, used it to find the failing `%%location_label%%`, and dropped it.
//! `blocksense-network/verus-lib` no longer does, and `venir` now writes a
//! `Counterexample` line. This module is the half that turns it into the
//! contract's shapes.
//!
//! Three things it is careful about, because a counterexample that is *wrong* is
//! worse than no counterexample:
//!
//! 1. **Order.** The snapshots arrive in the order the program reaches them --
//!    `air` iterates an insertion-ordered map that `var_to_const` fills as it
//!    walks the query. They are emitted as steps in that order and in no other.
//! 2. **Names.** An AIR variable is `name~<LocalId>@`, built by Verno's own
//!    `ast_var_into_var_ident`. [`demangle`] takes it apart. A name it cannot
//!    take apart keeps its raw spelling and reports no `LocalId`, rather than
//!    guessing one.
//! 3. **Completeness.** Names the encoding owns rather than the developer --
//!    type parameters, `%`-prefixed internals -- are not shown, and their
//!    presence downgrades the model to `partial` with the count stated. A model
//!    presented as `complete` when something was filtered out of it would be a
//!    claim about coverage that nothing checked.

use serde::{Deserialize, Serialize};

use super::{
    CounterexampleModel, CounterexampleStep, ModelBinding, ModelStatus, ObligationKind,
    SolverCounterexampleTrace, SourceLocation, StepKind, Trust, ViolatedObligation,
};

// ---------------------------------------------------------------------------
// The wire shape `venir` writes
// ---------------------------------------------------------------------------

/// One assignment, as `venir` writes it.
///
/// Mirrors `air::model::ModelBinding` in the pinned `verus-lib` revision. It is
/// re-declared here rather than depended on because Verno does not link `air`
/// and must not start doing so for four strings.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VenirBinding {
    /// The AIR-level variable name, as the query declared it.
    pub variable: String,
    /// The Z3 constant it was renamed to at this program point.
    pub constant: String,
    /// The solver's assignment, verbatim.
    pub value: String,
    /// The sort the solver gave the constant.
    pub typ: String,
}

/// The assignments in force at one recorded program point.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VenirSnapshot {
    pub snapshot_id: String,
    #[serde(default)]
    pub bindings: Vec<VenirBinding>,
}

/// `air::model::Counterexample`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VenirModel {
    #[serde(default)]
    pub parameters: Vec<VenirBinding>,
    #[serde(default)]
    pub snapshots: Vec<VenirSnapshot>,
    #[serde(default)]
    pub assert_id: Option<Vec<u64>>,
}

impl VenirModel {
    /// Whether the solver committed to anything at all. A model with no bindings
    /// is a located obligation and nothing more, and must not be offered as
    /// something to step through.
    pub fn is_populated(&self) -> bool {
        !self.parameters.is_empty() || self.snapshots.iter().any(|s| !s.bindings.is_empty())
    }
}

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/// `vir::def::SUFFIX_LOCAL_STMT` -- appended to every local's AIR name.
const SUFFIX_LOCAL_STMT: char = '@';
/// `vir::def::SUFFIX_RUSTC_ID` -- separates a name from the `LocalId` that
/// disambiguates it. Verno builds `VarIdent(name, RustcId(local_id))` in
/// `vir_gen::expr_to_vir::ast_var_into_var_ident`, so this is the seam.
const SUFFIX_RUSTC_ID: char = '~';
/// `vir::def::SUFFIX_TYPE_PARAM` / `SUFFIX_DECORATE_TYPE_PARAM`.
const SUFFIX_TYPE_PARAM: char = '&';
/// `vir::def::SUFFIX_PARAM`.
const SUFFIX_PARAM: char = '!';

/// A variable name, taken apart.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemangledName {
    /// What to show the developer.
    pub name: String,
    /// The Noir `LocalId`, when the AIR name carried one.
    pub local_id: Option<u32>,
    /// True when the name belongs to the encoding rather than to the program:
    /// a type parameter, or a `%`-prefixed internal such as `%return`.
    pub internal: bool,
}

/// Split an AIR-level variable name back into the developer's vocabulary.
///
/// `x~7@` becomes `("x", Some(7))`. A name that does not fit the shape keeps its
/// raw spelling and reports no `LocalId` -- inventing one would attach a value to
/// the wrong variable, which is the single worst thing this path can do.
pub fn demangle(air_name: &str) -> DemangledName {
    let internal = air_name.starts_with('%') || air_name.contains(SUFFIX_TYPE_PARAM);

    let trimmed =
        air_name.strip_suffix(SUFFIX_LOCAL_STMT).unwrap_or(air_name).trim_end_matches(SUFFIX_PARAM);

    // `parse` is the whole test for "is this a `LocalId`": it rejects an empty
    // suffix, a non-numeric one, and one too large for a `LocalId`, and each of
    // those must leave the raw name alone rather than half-strip it.
    match trimmed.rsplit_once(SUFFIX_RUSTC_ID) {
        Some((name, id)) if !name.is_empty() => match id.parse::<u32>() {
            Ok(local_id) => {
                DemangledName { name: name.to_string(), local_id: Some(local_id), internal }
            }
            Err(_) => DemangledName { name: trimmed.to_string(), local_id: None, internal },
        },
        _ => DemangledName { name: trimmed.to_string(), local_id: None, internal },
    }
}

fn binding_of(venir: &VenirBinding) -> Option<ModelBinding> {
    let demangled = demangle(&venir.variable);
    if demangled.internal {
        return None;
    }
    Some(ModelBinding {
        name: demangled.name,
        local_id: demangled.local_id,
        value: venir.value.clone(),
        type_name: Some(venir.typ.clone()),
        location: None,
    })
}

/// How many of `bindings` belong to the encoding rather than the program.
fn internal_count(bindings: &[VenirBinding]) -> usize {
    bindings.iter().filter(|b| demangle(&b.variable).internal).count()
}

// ---------------------------------------------------------------------------
// Obligations
// ---------------------------------------------------------------------------

/// Classify the verifier's own wording for what failed.
///
/// The raw text is kept whatever the answer, so nothing is lost when this
/// returns [`ObligationKind::Other`] -- which it does for anything not listed,
/// because inventing a category is worse than saying "other".
pub fn classify_obligation(message: &str) -> ObligationKind {
    let lower = message.to_ascii_lowercase();
    if lower.contains("postcondition") {
        ObligationKind::Postcondition
    } else if lower.contains("precondition") {
        ObligationKind::Precondition
    } else if lower.contains("invariant") {
        ObligationKind::LoopInvariant
    } else if lower.contains("decreases") {
        ObligationKind::LoopDecreases
    } else if lower.contains("overflow") || lower.contains("underflow") {
        ObligationKind::ArithmeticOverflow
    } else if lower.contains("assert") {
        ObligationKind::Assertion
    } else {
        ObligationKind::Other
    }
}

// ---------------------------------------------------------------------------
// The trace
// ---------------------------------------------------------------------------

/// What the caller knows about the obligation the model violates.
pub struct ObligationInfo {
    pub message: String,
    pub location: Option<SourceLocation>,
}

/// Build the contract's counterexample trace from one `venir` model.
///
/// Returns `None` when the model carries no values: a trace with no steps and no
/// bindings would pass the wire rules and then be offered to a developer as
/// something to walk through. `hasSteppableCounterexample` is the consumer's
/// gate; this is the producer's half of the same rule.
pub fn trace_from_model(
    id: impl Into<String>,
    finding_id: impl Into<String>,
    model: &VenirModel,
    obligation: ObligationInfo,
) -> Option<SolverCounterexampleTrace> {
    if !model.is_populated() {
        return None;
    }

    let mut steps: Vec<CounterexampleStep> = Vec::new();
    let mut all_bindings: Vec<ModelBinding> = Vec::new();
    let mut filtered = internal_count(&model.parameters);

    let parameter_bindings: Vec<ModelBinding> =
        model.parameters.iter().filter_map(binding_of).collect();
    if !parameter_bindings.is_empty() {
        all_bindings.extend(parameter_bindings.iter().cloned());
        steps.push(CounterexampleStep {
            index: steps.len(),
            kind: StepKind::Assumption,
            location: None,
            description: "the inputs the solver chose".to_string(),
            bindings: parameter_bindings,
            taken: None,
            iteration: None,
            path_condition: None,
        });
    }

    // In the order the program reaches them. `air` iterates an insertion-ordered
    // map that `var_to_const` fills as it walks the query, so this is the path
    // the model forces and not an alphabetical accident.
    for snapshot in &model.snapshots {
        filtered += internal_count(&snapshot.bindings);
        let bindings: Vec<ModelBinding> = snapshot.bindings.iter().filter_map(binding_of).collect();
        if bindings.is_empty() {
            continue;
        }
        all_bindings.extend(bindings.iter().cloned());
        steps.push(CounterexampleStep {
            index: steps.len(),
            kind: StepKind::Assignment,
            // The snapshot-to-span map (`SnapPos`) is built in `vir`/`rust_verify`
            // and is not carried across the `venir` boundary, so a step knows
            // *what* the values are and not *where*. Saying nothing is the only
            // honest answer; a guessed line would put a value against code that
            // did not produce it.
            location: None,
            description: format!("at program point `{}`", snapshot.snapshot_id),
            bindings,
            taken: None,
            iteration: None,
            path_condition: None,
        });
    }

    // Exactly one violation step, and it is last: the contract allows at most one
    // and the consumer marks it as the first violated obligation.
    steps.push(CounterexampleStep {
        index: steps.len(),
        kind: StepKind::Violation,
        location: obligation.location.clone(),
        description: obligation.message.clone(),
        bindings: Vec::new(),
        taken: None,
        iteration: None,
        path_condition: None,
    });

    let (status, absent_reason) = if filtered == 0 {
        (ModelStatus::Complete, None)
    } else {
        (
            ModelStatus::Partial,
            Some(format!(
                "{filtered} of the solver's assignments name variables the VIR encoding \
                 introduced rather than variables the developer wrote (type parameters and \
                 `%`-prefixed internals) and are not shown"
            )),
        )
    };

    Some(SolverCounterexampleTrace {
        id: id.into(),
        finding_id: finding_id.into(),
        trust: Trust::diagnostic_only(
            "the values are the SMT solver's own model of the query, carried across \
             unchanged; that the solver could not discharge the obligation is not a proof \
             the program is wrong",
        ),
        model: CounterexampleModel { status, absent_reason, bindings: all_bindings },
        steps,
        violated_obligation: Some(ViolatedObligation {
            kind: classify_obligation(&obligation.message),
            raw_kind: obligation.message.clone(),
            location: obligation.location,
            message: obligation.message,
        }),
        solver_query_id: None,
        // Always false. A solver model is not an execution that happened.
        is_recorded_execution: false,
    })
}
