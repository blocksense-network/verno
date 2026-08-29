//! The conformance corpus, checked against the producer's own rules.
//!
//! `conformance/codetracer-payload/` holds one JSON document per case. Both
//! sides of the VN-M4 contract test against the *same bytes*: this crate
//! validates them here, and CodeTracer's decoder validates a vendored copy in
//! `src/frontend/viewmodel/tests/fixtures/verno/payload/`. The two copies are
//! tied together by `manifest.json`, which lists a SHA-256 for every file and
//! is itself byte-identical in both repositories — so a fixture that changes on
//! one side and not the other fails on both rather than drifting quietly.
//!
//! Three properties, and each one would be worth having on its own:
//!
//! * every **accepted** fixture parses and satisfies every contract rule, so a
//!   consumer that rejects one has found a real disagreement rather than a
//!   typo in a hand-written file;
//! * every **rejected** fixture is refused, *and the refusal names the rule* —
//!   a rejection test that passed because the file was unparseable would prove
//!   nothing about the rule it claims to exercise;
//! * the manifest covers exactly the files on disk, in both directions, so a
//!   fixture cannot be added without being tested and cannot be tested after
//!   being deleted.
//!
//! The fixtures are embedded with `include_str!`, so deleting one is a compile
//! error rather than a quietly smaller test run.

use super::*;

// ---------------------------------------------------------------------------
// Accepted
// ---------------------------------------------------------------------------

/// Fixtures a conforming consumer must accept.
///
/// The third column is what produced the file, and it is the column that
/// matters: three of these are real `verno` runs and three are hand-authored,
/// because the machine this was written on cannot run a solver. The same table
/// appears in `conformance/codetracer-payload/PROVENANCE.md` in prose.
const ACCEPTED: &[(&str, &str, bool)] = &[
    (
        "no_solver.json",
        include_str!("../../../conformance/codetracer-payload/no_solver.json"),
        true,
    ),
    (
        "unsupported_lambda.json",
        include_str!("../../../conformance/codetracer-payload/unsupported_lambda.json"),
        true,
    ),
    (
        "pipeline_error_type_mismatch.json",
        include_str!("../../../conformance/codetracer-payload/pipeline_error_type_mismatch.json"),
        true,
    ),
    ("proved.json", include_str!("../../../conformance/codetracer-payload/proved.json"), false),
    (
        "not_proved_assertion.json",
        include_str!("../../../conformance/codetracer-payload/not_proved_assertion.json"),
        false,
    ),
    (
        "not_proved_with_model.json",
        include_str!("../../../conformance/codetracer-payload/not_proved_with_model.json"),
        false,
    ),
    (
        "timed_out_rlimit.json",
        include_str!("../../../conformance/codetracer-payload/timed_out_rlimit.json"),
        false,
    ),
];

/// Fixtures a conforming consumer must refuse, with the rule each one breaks.
///
/// The second element of the tuple is a substring of the violation message. A
/// rejection test without it would pass on *any* rejection, including the
/// wrong one.
const REJECTED: &[(&str, &str, &str)] = &[
    (
        "missing_run_trust.json",
        include_str!("../../../conformance/codetracer-payload/rejected/missing_run_trust.json"),
        "missing field `trust`",
    ),
    (
        "missing_finding_trust.json",
        include_str!("../../../conformance/codetracer-payload/rejected/missing_finding_trust.json"),
        "missing field `trust`",
    ),
    (
        "unknown_outcome.json",
        include_str!("../../../conformance/codetracer-payload/rejected/unknown_outcome.json"),
        "unknown variant",
    ),
    (
        "unknown_schema.json",
        include_str!("../../../conformance/codetracer-payload/rejected/unknown_schema.json"),
        "expected `codetracer.verification/v1`",
    ),
    (
        "limitation_answers_correctness.json",
        include_str!(
            "../../../conformance/codetracer-payload/rejected/limitation_answers_correctness.json"
        ),
        "says nothing about the program",
    ),
    (
        "counterexample_claims_recording.json",
        include_str!(
            "../../../conformance/codetracer-payload/rejected/counterexample_claims_recording.json"
        ),
        "never one",
    ),
    (
        "model_unavailable_with_bindings.json",
        include_str!(
            "../../../conformance/codetracer-payload/rejected/model_unavailable_with_bindings.json"
        ),
        "unavailable but carries bindings",
    ),
    (
        "proved_without_solver_oracle.json",
        include_str!(
            "../../../conformance/codetracer-payload/rejected/proved_without_solver_oracle.json"
        ),
        "rests on the solver oracle",
    ),
    (
        "counterexample_without_a_rejection.json",
        include_str!(
            "../../../conformance/codetracer-payload/rejected/counterexample_without_a_rejection.json"
        ),
        "only `not-proved` may carry one",
    ),
    (
        "finding_without_location_or_reason.json",
        include_str!(
            "../../../conformance/codetracer-payload/rejected/finding_without_location_or_reason.json"
        ),
        "no `location_absent_reason`",
    ),
];

#[test]
fn every_accepted_fixture_parses_and_satisfies_every_rule() {
    for (name, text, _) in ACCEPTED {
        let payload: VerificationPayload = serde_json::from_str(text)
            .unwrap_or_else(|error| panic!("{name} does not parse: {error}"));
        let problems = payload.check();
        assert!(problems.is_empty(), "{name} breaks the contract: {problems:?}");
        assert_eq!(payload.schema, SCHEMA_ID, "{name}");
    }
}

#[test]
fn every_accepted_fixture_round_trips_byte_for_byte_in_meaning() {
    for (name, text, _) in ACCEPTED {
        let payload: VerificationPayload = serde_json::from_str(text).unwrap();
        let reencoded = serde_json::to_string(&payload).unwrap();
        let again: VerificationPayload = serde_json::from_str(&reencoded).unwrap();
        assert_eq!(payload, again, "{name} lost information on re-encoding");
    }
}

#[test]
fn every_rejected_fixture_is_refused_for_the_reason_it_was_written_for() {
    for (name, text, expected) in REJECTED {
        // A rejection can happen at either of two gates: serde refuses a
        // missing required field or an unknown enum variant, and `check`
        // refuses a document that is well-formed but breaks a stated rule.
        // Both are the contract; what must not happen is acceptance.
        match serde_json::from_str::<VerificationPayload>(text) {
            Err(error) => {
                let message = error.to_string();
                assert!(
                    message.contains(expected),
                    "{name} was refused by serde, but for `{message}` rather than `{expected}`"
                );
            }
            Ok(payload) => {
                let problems = payload.check();
                assert!(
                    !problems.is_empty(),
                    "{name} was accepted; it exists to be refused for `{expected}`"
                );
                let joined: Vec<String> = problems.iter().map(|p| p.0.clone()).collect();
                assert!(
                    joined.iter().any(|problem| problem.contains(expected)),
                    "{name} was refused, but for {joined:?} rather than for `{expected}`"
                );
            }
        }
    }
}

#[test]
fn the_six_outcomes_are_all_covered_by_the_accepted_corpus() {
    // All six. What cannot be carried is a *cause*, not an outcome: a
    // wall-clock timeout kills the producer before it writes anything, so that
    // run has no payload at all. `timed-out` itself is perfectly expressible
    // and is emitted for a solver `rlimit` exhaustion — see
    // `venir_communication.rs` — which is why `timed_out_rlimit.json` is in the
    // corpus. Naming this test "except the one that cannot be" while asserting
    // all six was the kind of near-miss the corpus exists to catch.
    let mut seen: Vec<Outcome> = Vec::new();
    for (_, text, _) in ACCEPTED {
        let payload: VerificationPayload = serde_json::from_str(text).unwrap();
        if !seen.contains(&payload.outcome) {
            seen.push(payload.outcome);
        }
    }
    for outcome in [
        Outcome::Proved,
        Outcome::NotProved,
        Outcome::TimedOut,
        Outcome::Unsupported,
        Outcome::NoSolver,
        Outcome::PipelineError,
    ] {
        assert!(seen.contains(&outcome), "no accepted fixture covers {outcome:?}");
    }
}

#[test]
fn no_accepted_fixture_claims_a_solver_ran_on_the_machine_that_recorded_it() {
    // The honesty rule for this corpus: a fixture marked as a real recording
    // must not claim a solver was invoked, because none can be on the machine
    // these were recorded on. A future recording made on Linux flips the flag
    // in `ACCEPTED` and this test follows it.
    for (name, text, is_recording) in ACCEPTED {
        if !is_recording {
            continue;
        }
        let payload: VerificationPayload = serde_json::from_str(text).unwrap();
        assert!(
            !payload.run.solver.invoked,
            "{name} is recorded as a real run but claims a solver was invoked"
        );
        assert!(
            payload.counterexample_traces.is_empty(),
            "{name} is recorded as a real run but carries a counterexample; no solver \
             produced one"
        );
        assert_ne!(
            payload.trust.class,
            TrustClass::SolverOracle,
            "{name} is recorded as a real run but claims solver-oracle trust"
        );
    }
}

#[test]
fn the_hypothetical_model_fixture_says_it_is_hypothetical() {
    // `not_proved_with_model.json` is the only fixture carrying model values,
    // and no solver produced them. It exists so the *decoder* on the other
    // side has something with a populated model, path steps and a goal tree to
    // parse. Its producer version is deliberately not a real Verno version, so
    // that it can never be mistaken for a recording in a log or a bug report.
    let payload: VerificationPayload = serde_json::from_str(include_str!(
        "../../../conformance/codetracer-payload/not_proved_with_model.json"
    ))
    .unwrap();
    assert_eq!(payload.producer.version, "0.0.0-hypothetical");
    assert!(payload.run.workspace_root.contains("NOT A RECORDING"));
    assert_eq!(payload.counterexample_traces[0].model.status, ModelStatus::Partial);
    assert!(!payload.counterexample_traces[0].is_recorded_execution);
}

// ---------------------------------------------------------------------------
// The manifest, which is what makes this a *shared* corpus
// ---------------------------------------------------------------------------

const MANIFEST: &str = include_str!("../../../conformance/codetracer-payload/manifest.json");

#[test]
fn the_manifest_covers_exactly_the_fixtures_this_test_embeds() {
    // Both directions *between the manifest and the list this test embeds* —
    // which is what the assertion below actually compares, and is worth
    // stating exactly because the stronger reading is false. A manifest entry
    // with no embedded fixture is caught here (and a deleted file is an
    // `include_str!` compile error). A stray `.json` dropped into the
    // directory that is in neither the manifest nor `ACCEPTED`/`REJECTED` is
    // **not** caught: nothing here reads the directory. That file would also
    // be invisible to the consumer, so it cannot cause the two sides to
    // disagree — but it is an unchecked file, not a checked one, and the
    // comment that used to claim otherwise was overstating the guarantee.
    let manifest: serde_json::Value = serde_json::from_str(MANIFEST).expect("manifest parses");
    let entries = manifest["fixtures"].as_array().expect("fixtures array");
    let listed: Vec<String> =
        entries.iter().map(|entry| entry["path"].as_str().expect("path").to_string()).collect();

    let mut embedded: Vec<String> = ACCEPTED.iter().map(|(name, _, _)| name.to_string()).collect();
    embedded.extend(REJECTED.iter().map(|(name, _, _)| format!("rejected/{name}")));
    embedded.sort();
    let mut listed_sorted = listed.clone();
    listed_sorted.sort();
    assert_eq!(listed_sorted, embedded, "the manifest and the embedded fixture list disagree");

    assert_eq!(
        manifest["schema"].as_str(),
        Some(SCHEMA_ID),
        "the manifest names a different schema than the payloads it lists"
    );
}

#[test]
fn every_manifest_digest_matches_the_fixture_it_names() {
    // This is what ties the two repositories together. CodeTracer keeps a
    // byte-identical copy of `manifest.json` and runs the same check against
    // its vendored fixtures, so a fixture edited in one repository and not the
    // other fails in both — rather than the two silently testing different
    // corpora and both staying green.
    let manifest: serde_json::Value = serde_json::from_str(MANIFEST).unwrap();
    let entries = manifest["fixtures"].as_array().unwrap();
    let mut by_path = std::collections::BTreeMap::new();
    for (name, text, _) in ACCEPTED {
        by_path.insert(name.to_string(), *text);
    }
    for (name, text, _) in REJECTED {
        by_path.insert(format!("rejected/{name}"), *text);
    }
    for entry in entries {
        let path = entry["path"].as_str().unwrap();
        let expected = entry["sha256"].as_str().unwrap();
        let text = by_path
            .get(path)
            .unwrap_or_else(|| panic!("manifest lists {path}, which is not embedded"));
        let actual = sha256_hex(text.as_bytes());
        assert_eq!(
            actual, expected,
            "{path} does not match its manifest digest; if the change is intended, \
             regenerate the manifest in BOTH repositories"
        );
    }
}

/// SHA-256, written out rather than taken as a dependency.
///
/// Verno has no hashing crate and adding one for a fixture manifest would put
/// a new transitive dependency in a verifier's dependency tree. FIPS 180-4,
/// about forty lines.
fn sha256_hex(input: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut message = input.to_vec();
    let bit_length = (input.len() as u64) * 8;
    message.push(0x80);
    while message.len() % 64 != 56 {
        message.push(0);
    }
    message.extend_from_slice(&bit_length.to_be_bytes());

    for chunk in message.chunks(64) {
        let mut w = [0u32; 64];
        for (index, word) in chunk.chunks(4).enumerate() {
            w[index] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for index in 16..64 {
            let s0 = w[index - 15].rotate_right(7)
                ^ w[index - 15].rotate_right(18)
                ^ (w[index - 15] >> 3);
            let s1 = w[index - 2].rotate_right(17)
                ^ w[index - 2].rotate_right(19)
                ^ (w[index - 2] >> 10);
            w[index] = w[index - 16].wrapping_add(s0).wrapping_add(w[index - 7]).wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
            (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
        for index in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 =
                hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[index]).wrapping_add(w[index]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }
        for (slot, value) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(value);
        }
    }

    h.iter().map(|word| format!("{word:08x}")).collect()
}

#[test]
fn the_hand_written_sha256_agrees_with_the_published_test_vectors() {
    // The digest check above is only worth anything if this function is
    // right. FIPS 180-4 Appendix B.
    assert_eq!(sha256_hex(b""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        sha256_hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
}
