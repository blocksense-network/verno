//! Tests for the VN-M4 payload contract.
//!
//! These run in CI: `cargo test -p formal_verification --lib --locked` is the
//! job that does not need `venir`, and none of the assertions below do either.
//!
//! What they establish, and what they cannot: they establish that the contract's
//! rules hold on values, that a document round-trips through JSON without loss,
//! and that a payload breaking any stated rule is refused *by the producer*
//! before it is written. They do not establish that a solver ever produced a
//! model — no solver runs on the machine this was written on. That gap is
//! recorded in `conformance/codetracer-payload/PROVENANCE.md`.

use super::emit::{
    NOIR_RELEASE, PayloadBuilder, line_and_column, solver_invoked, solver_unavailable,
    venir_oracle_footprint,
};
use super::*;

fn builder() -> PayloadBuilder {
    PayloadBuilder::new(
        Path::new("/tmp/example"),
        vec!["verno".to_string(), "formal-verify".to_string()],
    )
}

/// A minimal well-formed payload for the `no-solver` outcome — the only one
/// this machine can produce for a correct program.
fn no_solver_payload() -> VerificationPayload {
    let mut builder = builder();
    builder.set_package(Some("example".to_string()));
    builder.add_finding(
        FindingKind::SolverUnavailable,
        "The Noir to VIR pipeline completed; the solver was not started.",
        "Nothing was established either way.",
        None,
        "Failed to start the Venir binary",
        "no solver ran, so there is no obligation to point at",
        Trust::diagnostic_only("no solver was started"),
    );
    builder.finish(
        Outcome::NoSolver,
        "Noir -> VIR pipeline completed; `venir` not available",
        solver_unavailable("`venir` was not found on PATH"),
        None,
    )
}

fn not_proved_payload() -> VerificationPayload {
    let mut builder = builder();
    let finding = builder.add_finding(
        FindingKind::FailedObligation,
        "assertion failed",
        "assertion failed",
        None,
        "error: assertion failed",
        "recorded without a span for this test",
        Trust::diagnostic_only("the solver did not discharge this obligation"),
    );
    let mut payload =
        builder.finish(Outcome::NotProved, "assertion failed", solver_invoked(), None);
    payload.counterexample_traces.push(SolverCounterexampleTrace {
        id: "cex0".to_string(),
        finding_id: finding,
        trust: Trust::diagnostic_only("a solver model is not proof evidence"),
        model: CounterexampleModel::unavailable(
            "`venir` discards the model `air` hands it in `ValidityResult::Invalid`",
        ),
        steps: Vec::new(),
        violated_obligation: None,
        solver_query_id: None,
        is_recorded_execution: false,
    });
    payload
}

// ---------------------------------------------------------------------------
// The six outcomes
// ---------------------------------------------------------------------------

#[test]
fn all_six_outcomes_round_trip_through_json_as_themselves() {
    // The wire spellings must be `run-corpus.py`'s, or a CodeTracer report and
    // a corpus report stop being comparable without a translation table.
    let expected = [
        (Outcome::Proved, "proved"),
        (Outcome::NotProved, "not-proved"),
        (Outcome::TimedOut, "timed-out"),
        (Outcome::Unsupported, "unsupported"),
        (Outcome::NoSolver, "no-solver"),
        (Outcome::PipelineError, "pipeline-error"),
    ];
    for (outcome, spelling) in expected {
        let encoded = serde_json::to_string(&outcome).unwrap();
        assert_eq!(encoded, format!("\"{spelling}\""), "wire spelling changed");
        assert_eq!(outcome.as_str(), spelling);
        let decoded: Outcome = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded, outcome);
    }
}

#[test]
fn exactly_one_outcome_is_a_failed_proof() {
    let all = [
        Outcome::Proved,
        Outcome::NotProved,
        Outcome::TimedOut,
        Outcome::Unsupported,
        Outcome::NoSolver,
        Outcome::PipelineError,
    ];
    assert_eq!(all.iter().filter(|o| o.is_failed_proof()).count(), 1);
    assert_eq!(all.iter().filter(|o| o.answers_correctness()).count(), 2);
    assert!(Outcome::NotProved.is_failed_proof());
}

#[test]
fn the_six_finding_kinds_match_the_six_outcomes_one_for_one() {
    // The kind is derived from the outcome, once. Nothing downstream may
    // re-derive it, and this is the mapping both sides agree on.
    assert_eq!(FindingKind::for_outcome(Outcome::Unsupported), FindingKind::Limitation);
    assert_eq!(FindingKind::for_outcome(Outcome::NotProved), FindingKind::FailedObligation);
    assert_eq!(FindingKind::for_outcome(Outcome::TimedOut), FindingKind::BudgetExhausted);
    assert_eq!(FindingKind::for_outcome(Outcome::NoSolver), FindingKind::SolverUnavailable);
    assert_eq!(FindingKind::for_outcome(Outcome::PipelineError), FindingKind::PipelineError);
    assert_eq!(FindingKind::for_outcome(Outcome::Proved), FindingKind::Proved);
}

// ---------------------------------------------------------------------------
// Round-tripping
// ---------------------------------------------------------------------------

#[test]
fn a_payload_round_trips_without_loss() {
    let payload = not_proved_payload();
    let json = payload.to_json().expect("valid payload");
    let decoded: VerificationPayload = serde_json::from_str(&json).unwrap();
    assert_eq!(decoded, payload);
    assert_eq!(decoded.schema, SCHEMA_ID);
}

#[test]
fn the_producer_refuses_to_write_a_payload_that_breaks_its_own_contract() {
    // `to_json` checks before serialising, so a bug in a call site is a loud
    // error rather than a document a consumer will silently reject.
    let mut payload = no_solver_payload();
    payload.schema = "something.else/v9".to_string();
    let error = payload.to_json().expect_err("must refuse");
    assert!(error.0.contains("expected `codetracer.verification/v1`"), "{}", error.0);
}

// ---------------------------------------------------------------------------
// Trust
// ---------------------------------------------------------------------------

#[test]
fn a_trust_class_without_a_reason_is_refused() {
    let mut payload = no_solver_payload();
    payload.trust.reason = "   ".to_string();
    let problems = payload.check();
    assert!(problems.iter().any(|p| p.0.contains("no reason")), "{problems:?}");
}

#[test]
fn a_solver_oracle_claim_without_a_footprint_is_refused() {
    let mut payload = no_solver_payload();
    payload.trust = Trust {
        class: TrustClass::SolverOracle,
        reason: "trust me".to_string(),
        oracle_footprint: None,
    };
    let problems = payload.check();
    assert!(problems.iter().any(|p| p.0.contains("no oracle footprint")), "{problems:?}");
}

#[test]
fn a_solver_oracle_claim_without_a_solver_run_is_refused() {
    // The dangerous shape: a payload that says "the solver vouched for this"
    // on a machine where no solver process was ever started.
    let mut payload = no_solver_payload();
    payload.trust =
        Trust::solver_oracle("claims a solver answered", venir_oracle_footprint(&[], Some(0)));
    let problems = payload.check();
    assert!(problems.iter().any(|p| p.0.contains("no solver was invoked")), "{problems:?}");
}

#[test]
fn an_oracle_footprint_must_say_what_it_could_not_record() {
    let mut payload = no_solver_payload();
    payload.run.solver = solver_invoked();
    payload.outcome = Outcome::Proved;
    payload.findings.clear();
    let mut footprint = venir_oracle_footprint(&["--rlimit".into(), "10".into()], Some(0));
    footprint.statistics_absent_reason = None;
    payload.trust = Trust::solver_oracle("the solver said unsat", footprint);
    let problems = payload.check();
    assert!(
        problems.iter().any(|p| p.0.contains("no statistics and gives no reason")),
        "{problems:?}"
    );
}

#[test]
fn a_proved_run_must_rest_on_the_solver_oracle_and_say_so() {
    // `proved` with `diagnostic-only` trust would be a verdict resting on
    // nothing. `proved` with a footprint is the honest shape.
    let mut payload = no_solver_payload();
    payload.outcome = Outcome::Proved;
    payload.findings.clear();
    let problems = payload.check();
    assert!(problems.iter().any(|p| p.0.contains("rests on the solver oracle")), "{problems:?}");

    payload.run.solver = solver_invoked();
    payload.trust = Trust::solver_oracle(
        "Z3 answered unsat through Verus; nothing re-checked it",
        venir_oracle_footprint(&["--rlimit".into(), "10".into()], Some(0)),
    );
    assert!(payload.check().is_empty(), "{:?}", payload.check());
}

#[test]
fn a_failed_obligation_is_diagnostic_only_and_never_evidence_the_program_is_wrong() {
    // With quantifiers and a resource limit, "the solver did not discharge
    // this" is not "the program is wrong". The producer must not claim more.
    let payload = not_proved_payload();
    assert_eq!(payload.trust.class, TrustClass::DiagnosticOnly);
    assert!(payload.trust.reason.contains("not a proof the program is wrong"));
    assert!(payload.check().is_empty(), "{:?}", payload.check());
}

// ---------------------------------------------------------------------------
// A limitation can never wear an obligation's clothes
// ---------------------------------------------------------------------------

#[test]
fn a_limitation_cannot_appear_in_a_payload_that_answers_correctness() {
    // This is VN-M3's central property, restated as a wire rule. The check
    // exists so a future emitter cannot produce the document at all.
    let mut builder = builder();
    builder.add_finding(
        FindingKind::Limitation,
        "Verno does not support function types (lambdas, function values)",
        "a limitation of the verifier, not a failed proof",
        Some("function types (lambdas, function values)".to_string()),
        "not yet implemented: UNSUPPORTED: function types (lambdas, function values)",
        "Verno's todo!() panics carry a Rust position, never a Noir one",
        Trust::diagnostic_only("nothing was proved or disproved"),
    );
    let mut payload = builder.finish(
        Outcome::Unsupported,
        "UNSUPPORTED: function types",
        solver_unavailable("refused before the solver"),
        None,
    );
    assert!(payload.check().is_empty(), "{:?}", payload.check());

    // Now claim the run answered correctness, keeping the limitation.
    payload.outcome = Outcome::NotProved;
    let problems = payload.check();
    assert!(
        problems.iter().any(|p| p.0.contains("says nothing about the program")),
        "{problems:?}"
    );
}

#[test]
fn a_limitation_must_name_its_construct() {
    let mut builder = builder();
    builder.add_finding(
        FindingKind::Limitation,
        "Verno does not support something",
        "",
        None,
        "",
        "no Noir span",
        Trust::diagnostic_only("nothing was proved or disproved"),
    );
    let payload = builder.finish(
        Outcome::Unsupported,
        "unsupported",
        solver_unavailable("refused before the solver"),
        None,
    );
    let problems = payload.check();
    assert!(problems.iter().any(|p| p.0.contains("does not name the construct")), "{problems:?}");
}

#[test]
fn a_failed_obligation_cannot_appear_under_any_outcome_but_not_proved() {
    for outcome in [
        Outcome::Proved,
        Outcome::TimedOut,
        Outcome::Unsupported,
        Outcome::NoSolver,
        Outcome::PipelineError,
    ] {
        let mut payload = not_proved_payload();
        payload.counterexample_traces.clear();
        payload.outcome = outcome;
        let problems = payload.check();
        assert!(
            problems.iter().any(|p| p.0.contains("only `not-proved` may carry one")),
            "outcome {outcome:?} accepted a failed obligation: {problems:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Counterexamples
// ---------------------------------------------------------------------------

#[test]
fn an_unavailable_model_must_say_why_and_must_carry_no_bindings() {
    let mut payload = not_proved_payload();
    payload.counterexample_traces[0].model.absent_reason = None;
    assert!(
        payload.check().iter().any(|p| p.0.contains("no `absent_reason`")),
        "{:?}",
        payload.check()
    );

    let mut payload = not_proved_payload();
    payload.counterexample_traces[0].model.bindings.push(ModelBinding {
        name: "x".to_string(),
        local_id: Some(1),
        value: "10".to_string(),
        type_name: Some("i8".to_string()),
        location: None,
    });
    assert!(
        payload.check().iter().any(|p| p.0.contains("unavailable but carries bindings")),
        "{:?}",
        payload.check()
    );
}

#[test]
fn a_counterexample_can_never_claim_to_be_a_recorded_execution() {
    // The visualization spec's rule: "When no real execution exists, the
    // counterexample trace remains a visual diagnostic artifact and must not
    // be presented as recorded runtime evidence."
    let mut payload = not_proved_payload();
    payload.counterexample_traces[0].is_recorded_execution = true;
    assert!(payload.check().iter().any(|p| p.0.contains("never one")), "{:?}", payload.check());
}

#[test]
fn a_counterexample_cannot_be_attached_to_an_outcome_that_did_not_reject_anything() {
    for outcome in [Outcome::Proved, Outcome::TimedOut, Outcome::NoSolver] {
        let mut payload = not_proved_payload();
        payload.findings[0].kind = FindingKind::SolverUnavailable;
        payload.outcome = outcome;
        assert!(
            payload.check().iter().any(|p| p.0.contains("only `not-proved` may carry one")),
            "outcome {outcome:?} accepted a counterexample"
        );
    }
}

#[test]
fn a_counterexample_must_point_at_a_finding_that_exists() {
    let mut payload = not_proved_payload();
    payload.counterexample_traces[0].finding_id = "f99".to_string();
    assert!(
        payload.check().iter().any(|p| p.0.contains("unknown finding")),
        "{:?}",
        payload.check()
    );
}

#[test]
fn at_most_one_step_may_be_the_violation() {
    let mut payload = not_proved_payload();
    for index in 0..2 {
        payload.counterexample_traces[0].steps.push(CounterexampleStep {
            index,
            kind: StepKind::Violation,
            location: None,
            description: "violated".to_string(),
            bindings: Vec::new(),
            taken: None,
            iteration: None,
            path_condition: None,
        });
    }
    assert!(
        payload.check().iter().any(|p| p.0.contains("at most one may be")),
        "{:?}",
        payload.check()
    );
}

// ---------------------------------------------------------------------------
// Locations
// ---------------------------------------------------------------------------

#[test]
fn a_finding_with_no_location_must_say_why_it_has_none() {
    // The failure this prevents is a marker at line 1: a claim about code that
    // made no such claim.
    let mut payload = no_solver_payload();
    payload.findings[0].location_absent_reason = None;
    assert!(
        payload.check().iter().any(|p| p.0.contains("no `location_absent_reason`")),
        "{:?}",
        payload.check()
    );
}

#[test]
fn a_location_must_resolve_through_the_source_map() {
    let mut payload = no_solver_payload();
    payload.findings[0].location = Some(SourceLocation {
        file: "src/main.nr".to_string(),
        file_index: 7,
        start_line: 1,
        start_column: 1,
        end_line: 1,
        end_column: 2,
        byte_start: 0,
        byte_end: 1,
    });
    payload.findings[0].location_absent_reason = None;
    assert!(
        payload.check().iter().any(|p| p.0.contains("points at source-map file 7 of 0")),
        "{:?}",
        payload.check()
    );
}

#[test]
fn line_and_column_count_characters_the_way_the_reporter_does() {
    // codespan counts char boundaries from the start of the line, so a
    // non-ASCII character earlier on the line shifts the column by one, not by
    // its byte length. Verno's own diagnostics print those numbers; the
    // payload must agree with them or a merged view marks the wrong column.
    let source = "fn main() {\n    let \u{e9}x = 1;\n}\n";
    let byte_of_x = source.find('x').unwrap();
    let (line, column) = line_and_column(source, byte_of_x);
    assert_eq!(line, 2);
    // "    let é" is nine characters, so `x` is the tenth.
    assert_eq!(column, 10);
    assert_eq!(line_and_column(source, 0), (1, 1));
    // Past the end clamps rather than panicking.
    assert_eq!(line_and_column(source, 10_000).0, 4);
}

// ---------------------------------------------------------------------------
// Producer identity
// ---------------------------------------------------------------------------

#[test]
fn the_noir_release_constant_matches_the_pin() {
    // The payload states which Noir release it was produced against. If that
    // string and `Cargo.toml` drift, a consumer is told the wrong thing about
    // an artifact it may keep for a long time. `check-noir-pin.sh` guarantees
    // the manifest is self-consistent; this guarantees the constant tracks it.
    let manifest = include_str!("../../../Cargo.toml");
    let expected = format!("tag = \"{NOIR_RELEASE}\"");
    assert!(
        manifest.contains(&expected),
        "payload::emit::NOIR_RELEASE is `{NOIR_RELEASE}`, which does not appear as a \
         `{expected}` pin in the workspace Cargo.toml"
    );
    // And no *other* noir tag is pinned, which would make the single string a
    // lie even though it appears.
    for line in manifest.lines() {
        if line.contains("noir-lang/noir") && line.contains("tag = ") {
            assert!(line.contains(&expected), "a second Noir tag is pinned: {line}");
        }
    }
}

#[test]
fn the_payload_names_its_producer_and_the_language_release() {
    let payload = no_solver_payload();
    assert_eq!(payload.producer.name, "verno");
    assert_eq!(payload.producer.source_language, "noir");
    assert_eq!(payload.producer.language_release, NOIR_RELEASE);
    assert!(!payload.producer.version.is_empty());
}

#[test]
fn a_run_without_a_solver_must_say_why_there_was_none() {
    let mut payload = no_solver_payload();
    payload.run.solver.unavailable_reason = None;
    assert!(
        payload.check().iter().any(|p| p.0.contains("no `unavailable_reason`")),
        "{:?}",
        payload.check()
    );
}

#[test]
fn duplicate_finding_ids_are_refused() {
    let mut payload = no_solver_payload();
    let clone = payload.findings[0].clone();
    payload.findings.push(clone);
    assert!(
        payload.check().iter().any(|p| p.0.contains("duplicate finding id")),
        "{:?}",
        payload.check()
    );
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

#[test]
fn writing_a_payload_produces_a_complete_document_and_never_a_partial_one() {
    let directory = std::env::temp_dir().join(format!("verno-payload-{}", std::process::id()));
    let path = directory.join(REPORT_FILE_NAME);
    let payload = no_solver_payload();
    payload.write_to(&path).expect("write");
    let written = std::fs::read_to_string(&path).expect("read back");
    let decoded: VerificationPayload = serde_json::from_str(&written).expect("parse");
    assert_eq!(decoded, payload);
    // No temporary file is left behind.
    let leftovers: Vec<_> = std::fs::read_dir(&directory)
        .unwrap()
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.file_name().to_string_lossy().to_string())
        .filter(|name| name != REPORT_FILE_NAME)
        .collect();
    assert!(leftovers.is_empty(), "left behind {leftovers:?}");
    let _ = std::fs::remove_dir_all(&directory);
}

#[test]
fn writing_refuses_an_invalid_payload_rather_than_leaving_a_bad_file() {
    let directory = std::env::temp_dir().join(format!("verno-payload-bad-{}", std::process::id()));
    let path = directory.join(REPORT_FILE_NAME);
    let mut payload = no_solver_payload();
    payload.findings[0].location_absent_reason = None;
    let error = payload.write_to(&path).expect_err("must refuse");
    assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    assert!(!path.exists(), "a rejected payload was written anyway");
    let _ = std::fs::remove_dir_all(&directory);
}
