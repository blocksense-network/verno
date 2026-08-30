//! Checks for the counterexample half of the payload.
//!
//! The input to most of these is [`REAL_MODEL`]: a **real solver artifact**, the
//! verbatim line `air --print-model` wrote for a real z3 run. It is not a
//! hand-written approximation of one, and that matters more here than anywhere
//! else in this crate, because the failure this product cannot ship is a
//! confident answer that is sometimes wrong. If Verno's decoder disagreed with
//! what a solver actually emits, a fixture invented alongside the decoder would
//! agree with it anyway.
//!
//! Every check counts its assertions and prints the count, so a check that
//! stopped asserting shows up in the output instead of staying green.
//! `tests/run-counterexample-mutations.py` proves that each check kills the
//! mutation written for it.

use super::counterexample::*;
use super::emit::{PayloadBuilder, obligation_from, solver_invoked};
use super::*;

/// A counterexample model **produced by a real solver**.
///
/// Recorded on 2026-08-30 by running `air --print-model` (from
/// `blocksense-network/verus-lib` `vn-m5/counterexample-model`) against z3
/// 4.15.1 on this query, which is shaped the way Verno's `vir_gen` shapes one --
/// `VarIdent(name, RustcId(local_id))` lowers to `name~<id>`, and `sst_to_air`
/// appends `@`:
///
/// ```text
/// (check-valid
///   (declare-const n~1@ Int)
///   (declare-var total~2@ Int)
///   (declare-var doubled~3@ Int)
///   (block
///     (assume (= n~1@ 42))
///     (assign total~2@ (+ n~1@ 1))
///     (snapshot after_total)
///     (assign doubled~3@ (* total~2@ 2))
///     (snapshot after_doubled)
///     (assert (< doubled~3@ 0))))
/// ```
///
/// The failing execution is unique, so the values below are not one model among
/// many: `n = 42`, `total = 43`, `doubled = 86` is *the* execution that reaches
/// the assertion. `doubled = 0` at `after_total` is the variable before its
/// assignment. This is what makes the checks below correspondence checks rather
/// than shape checks -- they compare against an execution worked out by hand.
pub const REAL_MODEL: &str = r#"{"parameters":[{"variable":"n~1@","constant":"n~1@","value":"42","typ":"Int"}],"snapshots":[{"snapshot_id":"after_total","bindings":[{"variable":"total~2@","constant":"total~2@1","value":"43","typ":"Int"},{"variable":"doubled~3@","constant":"doubled~3@0","value":"0","typ":"Int"}]},{"snapshot_id":"after_doubled","bindings":[{"variable":"total~2@","constant":"total~2@1","value":"43","typ":"Int"},{"variable":"doubled~3@","constant":"doubled~3@1","value":"86","typ":"Int"}]}],"assert_id":null}"#;

fn real_model() -> VenirModel {
    serde_json::from_str(REAL_MODEL).expect("the recorded solver artifact still parses")
}

/// Counted assertions, so a check that stopped asserting is visible.
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
    fn that(&mut self, what: &str, cond: bool) {
        self.n += 1;
        assert!(cond, "[{}] {}", self.name, what);
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

fn obligation() -> ObligationInfo {
    ObligationInfo {
        message: "assertion failed".to_string(),
        location: Some(SourceLocation {
            file: "src/main.nr".to_string(),
            file_index: 0,
            start_line: 7,
            start_column: 5,
            end_line: 7,
            end_column: 24,
            byte_start: 120,
            byte_end: 139,
        }),
    }
}

fn trace() -> SolverCounterexampleTrace {
    trace_from_model("cx0", "f0", &real_model(), obligation())
        .expect("a populated model yields a trace")
}

fn binding<'a>(bindings: &'a [ModelBinding], name: &str) -> &'a ModelBinding {
    bindings
        .iter()
        .find(|b| b.name == name)
        .unwrap_or_else(|| panic!("no binding named {}: {:?}", name, bindings))
}

// ---------------------------------------------------------------------------
// W1 -- names
// ---------------------------------------------------------------------------

#[test]
fn w1_an_air_name_is_taken_back_apart_into_the_developer_s_vocabulary() {
    let mut c = Counted::new("W1");

    let d = demangle("total~2@");
    c.eq("the Noir name", d.name.as_str(), "total");
    c.eq("the LocalId", d.local_id, Some(2));
    c.that("not internal", !d.internal);

    // A local with no disambiguator, and a name with a two-digit id.
    c.eq("no `~` means no LocalId", demangle("plain@").local_id, None);
    c.eq("and the name survives", demangle("plain@").name.as_str(), "plain");
    c.eq("multi-digit ids parse", demangle("x~1234@").local_id, Some(1234));

    // Control: things that must NOT be read as a LocalId. Attaching a value to
    // the wrong variable is the single worst thing this path can do, so a name
    // that does not fit the shape keeps its raw spelling.
    c.eq("a non-numeric suffix is not an id", demangle("x~abc@").local_id, None);
    c.eq("and the raw name is kept", demangle("x~abc@").name.as_str(), "x~abc");
    c.eq("an empty suffix is not an id", demangle("x~@").local_id, None);
    c.eq("and leaves the name whole", demangle("x~@").name.as_str(), "x~");
    // A `~` with nothing before it is not a disambiguated name; taking the id
    // would leave a nameless binding carrying a value.
    c.eq("a leading `~` is not a disambiguator", demangle("~5@").local_id, None);
    c.eq("and its name is kept raw", demangle("~5@").name.as_str(), "~5");

    // Names the encoding owns rather than the developer.
    c.that("`%return` is internal", demangle("%return").internal);
    c.that("a type parameter is internal", demangle("A&").internal);
    c.that("an ordinary name is not", !demangle("n~1@").internal);

    c.done(15);
}

// ---------------------------------------------------------------------------
// W2 -- the trace, in program order
// ---------------------------------------------------------------------------

#[test]
fn w2_the_trace_walks_the_program_points_in_the_order_the_model_gave_them() {
    let mut c = Counted::new("W2");
    let trace = trace();

    let kinds: Vec<StepKind> = trace.steps.iter().map(|s| s.kind).collect();
    c.eq(
        "inputs, then one step per program point, then the violation",
        kinds,
        vec![StepKind::Assumption, StepKind::Assignment, StepKind::Assignment, StepKind::Violation],
    );

    // The order is the model's order, which is the order the program reaches
    // those points. `after_doubled` sorts before `after_total`, so a decoder that
    // sorted -- or that iterated a hash map -- would fail here.
    c.eq(
        "the first program point is the one the program reaches first",
        trace.steps[1].description.as_str(),
        "at program point `after_total`",
    );
    c.eq(
        "and the second is the second",
        trace.steps[2].description.as_str(),
        "at program point `after_doubled`",
    );

    let indices: Vec<usize> = trace.steps.iter().map(|s| s.index).collect();
    c.eq("indices are 0..n in order", indices, vec![0, 1, 2, 3]);
    c.done(4);
}

// ---------------------------------------------------------------------------
// W3 -- the correspondence
// ---------------------------------------------------------------------------

#[test]
fn w3_the_values_are_the_values_the_failing_execution_computes() {
    let mut c = Counted::new("W3");
    let trace = trace();

    // The inputs the solver chose.
    let n = binding(&trace.steps[0].bindings, "n");
    c.eq("n is the pinned input", n.value.as_str(), "42");
    c.eq("carrying its LocalId", n.local_id, Some(1));
    c.eq("and the solver's sort", n.type_name.as_deref(), Some("Int"));

    // After `total = n + 1`. `doubled` is still at its pre-assignment value,
    // which is a fact about the execution and not noise.
    let after_total = &trace.steps[1].bindings;
    c.eq("total is n + 1", binding(after_total, "total").value.as_str(), "43");
    c.eq("doubled is not yet assigned", binding(after_total, "doubled").value.as_str(), "0");

    // After `doubled = total * 2`.
    let after_doubled = &trace.steps[2].bindings;
    c.eq("total is unchanged", binding(after_doubled, "total").value.as_str(), "43");
    c.eq("doubled is total * 2", binding(after_doubled, "doubled").value.as_str(), "86");

    // And that value is why the obligation `doubled < 0` failed.
    c.that(
        "the model violates the obligation",
        binding(after_doubled, "doubled").value.parse::<i64>().unwrap() >= 0,
    );

    // Every step's bindings also appear in the flat model, so a consumer that
    // reads only `model.bindings` sees the same values.
    c.eq("the flat model carries every binding", trace.model.bindings.len(), 5);
    c.eq(
        "including the final value of doubled",
        trace.model.bindings.iter().filter(|b| b.name == "doubled" && b.value == "86").count(),
        1,
    );
    c.done(10);
}

// ---------------------------------------------------------------------------
// W4 -- the gate
// ---------------------------------------------------------------------------

#[test]
fn w4_control_a_model_with_no_values_yields_no_trace() {
    let mut c = Counted::new("W4");

    c.that("an empty model is not populated", !VenirModel::default().is_populated());
    c.eq(
        "and yields no trace at all",
        trace_from_model("cx0", "f0", &VenirModel::default(), obligation()).is_none(),
        true,
    );

    // A model whose only bindings are the encoding's own is *populated* but has
    // nothing to show a developer, and must not become a steppable trace either.
    let internal_only = VenirModel {
        parameters: vec![VenirBinding {
            variable: "%return".to_string(),
            constant: "%return".to_string(),
            value: "0".to_string(),
            typ: "Int".to_string(),
        }],
        ..VenirModel::default()
    };
    let trace = trace_from_model("cx0", "f0", &internal_only, obligation())
        .expect("a populated model still yields a trace");
    c.eq("no bindings survive filtering", trace.model.bindings.len(), 0);
    c.eq("so the only step is the violation", trace.steps.len(), 1);
    c.eq("and the model is not complete", trace.model.status, ModelStatus::Partial);

    // Control: the real model does produce one.
    c.that("while the real model is populated", real_model().is_populated());
    c.done(6);
}

// ---------------------------------------------------------------------------
// W5 -- never presented as a recording
// ---------------------------------------------------------------------------

#[test]
fn w5_a_counterexample_is_never_a_recorded_execution() {
    let mut c = Counted::new("W5");
    let trace = trace();
    c.that("is_recorded_execution is false", !trace.is_recorded_execution);
    c.eq(
        "and stays false through JSON",
        {
            let json = serde_json::to_value(&trace).unwrap();
            json["is_recorded_execution"].clone()
        },
        serde_json::json!(false),
    );
    c.eq(
        "a solver model is diagnostic-only, never solver-oracle",
        trace.trust.class,
        TrustClass::DiagnosticOnly,
    );
    c.that("and says why", !trace.trust.reason.trim().is_empty());
    c.done(4);
}

// ---------------------------------------------------------------------------
// W6 -- completeness is claimed only when it is true
// ---------------------------------------------------------------------------

#[test]
fn w6_filtering_downgrades_the_model_and_says_how_much() {
    let mut c = Counted::new("W6");

    // Control: nothing filtered.
    let trace = trace();
    c.eq("a model with no internals is complete", trace.model.status, ModelStatus::Complete);
    c.eq("and needs no reason", trace.model.absent_reason, None);

    let mut with_internals = real_model();
    with_internals.parameters.push(VenirBinding {
        variable: "A&".to_string(),
        constant: "A&".to_string(),
        value: "$x!0".to_string(),
        typ: "Dcr".to_string(),
    });
    let trace = trace_from_model("cx0", "f0", &with_internals, obligation()).unwrap();
    c.eq("one filtered binding downgrades the model", trace.model.status, ModelStatus::Partial);
    let reason = trace.model.absent_reason.clone().expect("a partial model states a reason");
    c.that("and the reason counts them", reason.starts_with("1 of the solver's assignments"));
    c.eq("the filtered binding is not shown", trace.model.bindings.len(), 5);
    c.done(5);
}

// ---------------------------------------------------------------------------
// W7 -- the violated obligation
// ---------------------------------------------------------------------------

#[test]
fn w7_the_first_violated_obligation_is_marked_once_and_located() {
    let mut c = Counted::new("W7");
    let trace = trace();

    let violations: Vec<&CounterexampleStep> =
        trace.steps.iter().filter(|s| s.kind == StepKind::Violation).collect();
    c.eq("exactly one step is the violation", violations.len(), 1);
    c.eq("and it is the last one", violations[0].index, trace.steps.len() - 1);
    c.eq(
        "it points at the obligation's line",
        violations[0].location.as_ref().map(|l| l.start_line),
        Some(7),
    );

    let obligation = trace.violated_obligation.as_ref().expect("the trace names the obligation");
    c.eq("classified from the verifier's wording", obligation.kind, ObligationKind::Assertion);
    c.eq("keeping the raw wording", obligation.raw_kind.as_str(), "assertion failed");
    c.eq(
        "and the same location as the step",
        obligation.location.as_ref().map(|l| l.byte_start),
        Some(120),
    );

    // The classifier, and its fallback. `Other` is not a failure: it is the
    // answer when inventing a category would be worse.
    c.eq(
        "postcondition",
        classify_obligation("postcondition not satisfied"),
        ObligationKind::Postcondition,
    );
    c.eq(
        "precondition",
        classify_obligation("precondition not satisfied"),
        ObligationKind::Precondition,
    );
    c.eq(
        "invariant",
        classify_obligation("invariant not satisfied"),
        ObligationKind::LoopInvariant,
    );
    c.eq(
        "overflow",
        classify_obligation("possible arithmetic overflow"),
        ObligationKind::ArithmeticOverflow,
    );
    c.eq(
        "anything else is `other`",
        classify_obligation("the moon is made of cheese"),
        ObligationKind::Other,
    );
    c.done(11);
}

// ---------------------------------------------------------------------------
// W8 -- the whole payload, through the producer's own validator
// ---------------------------------------------------------------------------

/// Two findings, and the counterexample belongs to the **second**. A payload
/// with one finding cannot tell "the finding named" from "the first finding".
fn payload_with_counterexample(outcome: Outcome) -> (VerificationPayload, String) {
    let mut builder = PayloadBuilder::new(
        Path::new("/tmp/example"),
        vec!["verno".to_string(), "formal-verify".to_string()],
    );
    let _first = builder.add_finding(
        FindingKind::for_outcome(outcome),
        "precondition not satisfied",
        "precondition not satisfied",
        None,
        "error: precondition not satisfied",
        "recorded without a span for this check",
        Trust::diagnostic_only("the solver did not discharge this obligation"),
    );
    let second = builder.add_finding(
        FindingKind::for_outcome(outcome),
        "assertion failed",
        "assertion failed",
        None,
        "error: assertion failed",
        "recorded without a span for this check",
        Trust::diagnostic_only("the solver did not discharge this obligation"),
    );
    builder.add_counterexample(&second, &real_model());
    (builder.finish(outcome, "assertion failed", solver_invoked(), None), second)
}

#[test]
fn w8_a_payload_carrying_the_model_passes_the_producer_s_own_rules() {
    let mut c = Counted::new("W8");

    let (payload, attached_to) = payload_with_counterexample(Outcome::NotProved);
    // Printed under `--nocapture` because this is the exact document the
    // CodeTracer-side checks decode. CodeTracer's
    // `tests/fixtures/verno/counterexample/verno_emitted_solver_model.json` is
    // this output with three machine-specific fields substituted (the two
    // timestamps and `run.workspace_root`, which is set to a string saying it is
    // not a recording); its PROVENANCE.md names this command. Producing that
    // document here rather than writing it there by hand is what makes the two
    // sides a boundary rather than two guesses.
    println!("{}", payload.to_json().unwrap_or_default());
    c.eq("one counterexample was attached", payload.counterexample_traces.len(), 1);
    c.eq("and the payload breaks no rule", payload.check(), Vec::new());
    c.that("so it serialises", payload.to_json().is_ok());

    // It refers to the finding it was asked for, which is not the first one.
    c.eq(
        "the trace names the finding it was attached to",
        payload.counterexample_traces[0].finding_id.as_str(),
        attached_to.as_str(),
    );
    c.eq("and that is the second finding, not the first", attached_to.as_str(), "f1");
    c.eq(
        "so the obligation it marks is the second finding's",
        payload.counterexample_traces[0].violated_obligation.as_ref().map(|o| o.raw_kind.as_str()),
        Some("assertion failed"),
    );

    // The obligation is read off the finding, so the marked violation and the
    // rendered diagnostic cannot point at different places.
    let located = Finding {
        id: "f9".to_string(),
        kind: FindingKind::FailedObligation,
        message: "assertion failed".to_string(),
        detail: "assertion failed".to_string(),
        construct: None,
        location: obligation().location.clone(),
        location_absent_reason: None,
        excerpt: String::new(),
        trust: Trust::diagnostic_only("for this check"),
    };
    c.eq(
        "the obligation keeps the finding's location",
        obligation_from(&located).location.map(|l| l.start_line),
        Some(7),
    );

    // Mutation arm, in the check: the same trace under an outcome that does not
    // answer correctness is refused, by name.
    let (mut wrong, _) = payload_with_counterexample(Outcome::NotProved);
    wrong.outcome = Outcome::TimedOut;
    let problems = wrong.check();
    c.that("a counterexample under `timed-out` is refused", !problems.is_empty());
    c.that(
        "and the refusal names the rule",
        problems.iter().any(|p| {
            p.0.contains("only `not-proved` may carry one") && p.0.contains("counterexample")
        }),
    );

    // And a trace claiming to be a recording is refused, whatever else is right.
    let (mut lying, _) = payload_with_counterexample(Outcome::NotProved);
    lying.counterexample_traces[0].is_recorded_execution = true;
    c.that(
        "a trace claiming to be a recording is refused",
        lying.check().iter().any(|p| p.0.contains("claims to be a recorded execution")),
    );
    c.done(10);
}

// ---------------------------------------------------------------------------
// W9 -- the recorded solver artifact is still the shape `air` writes
// ---------------------------------------------------------------------------

#[test]
fn w9_the_recorded_solver_artifact_decodes_field_for_field() {
    let mut c = Counted::new("W9");
    let model = real_model();

    c.eq("one parameter", model.parameters.len(), 1);
    c.eq("named as the query declared it", model.parameters[0].variable.as_str(), "n~1@");
    c.eq("read under its own constant", model.parameters[0].constant.as_str(), "n~1@");
    c.eq("two program points", model.snapshots.len(), 2);
    c.eq("in program order", model.snapshots[0].snapshot_id.as_str(), "after_total");
    c.eq("second point", model.snapshots[1].snapshot_id.as_str(), "after_doubled");
    c.eq("each with two variables", model.snapshots[0].bindings.len(), 2);

    // The renamed constant differs between the two points for the variable that
    // changed, and not for the one that did not. That is the property that says
    // the model is positioned rather than flat.
    let total_first = &model.snapshots[0].bindings[0];
    let total_second = &model.snapshots[1].bindings[0];
    let doubled_first = &model.snapshots[0].bindings[1];
    let doubled_second = &model.snapshots[1].bindings[1];
    c.eq(
        "total's constant is the same at both",
        total_first.constant.as_str(),
        total_second.constant.as_str(),
    );
    c.that("doubled's is not", doubled_first.constant != doubled_second.constant);
    c.eq("this query carried no assert-id", model.assert_id, None);
    c.done(10);
}
