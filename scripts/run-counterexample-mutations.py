#!/usr/bin/env python3
"""Mutation harness for the counterexample checks (VN-M5).

Each mutation patches one line of the product and requires that the **named**
check fails. A mutation killed by some other check is reported as MISDIRECTED
and counts as a failure of this harness, because it means the check written for
it does not do its job. Mutations no check can kill are listed in
DECLARED_SURVIVORS with the reason at the line, and it is an error if one of
them starts dying -- that means the reason has gone stale.

Covers three files:
  * `formal_verification/src/payload/counterexample.rs` -- names, order,
    completeness, the obligation;
  * `formal_verification/src/payload/emit.rs` -- attaching a trace to a finding;
  * `formal_verification/src/venir_communication.rs` -- attaching a model to the
    error it explains, which is the only thing tying the two together on a wire
    where the model is a separate line.

Per `codetracer-specs/Testing/Verification-Harness-Traps.md`: the verdict comes
from the parsed per-test result lines, never from the exit code, and a run that
produced no result lines is a harness failure rather than a kill.

Usage:  ./scripts/run-counterexample-mutations.py
"""

import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CX = "formal_verification/src/payload/counterexample.rs"
EMIT = "formal_verification/src/payload/emit.rs"
COMM = "formal_verification/src/venir_communication.rs"

W1 = "w1_an_air_name_is_taken_back_apart_into_the_developer_s_vocabulary"
W2 = "w2_the_trace_walks_the_program_points_in_the_order_the_model_gave_them"
W3 = "w3_the_values_are_the_values_the_failing_execution_computes"
W4 = "w4_control_a_model_with_no_values_yields_no_trace"
W5 = "w5_a_counterexample_is_never_a_recorded_execution"
W6 = "w6_filtering_downgrades_the_model_and_says_how_much"
W7 = "w7_the_first_violated_obligation_is_marked_once_and_located"
W8 = "w8_a_payload_carrying_the_model_passes_the_producer_s_own_rules"
W9 = "w9_the_recorded_solver_artifact_decodes_field_for_field"
P1 = "p1_a_model_attaches_to_the_error_that_follows_it"
P2 = "p2_a_note_between_a_model_and_its_error_does_not_absorb_it"
P3 = "p3_an_unattached_model_is_dropped"


@dataclass
class Mutation:
    id: str
    path: str
    find: str
    replace: str
    killer: str
    why: str = ""


MUTATIONS = [
    # --- names -------------------------------------------------------------
    Mutation(
        "X1", CX,
        "                DemangledName { name: name.to_string(), local_id: Some(local_id), internal }",
        "                DemangledName { name: name.to_string(), local_id: None, internal }",
        W1,
    ),
    Mutation(
        "X2", CX,
        "    let internal = air_name.starts_with('%') || air_name.contains(SUFFIX_TYPE_PARAM);",
        "    let internal = false;",
        W1,
    ),
    Mutation(
        "X3", CX,
        "        Some((name, id)) if !name.is_empty() => match id.parse::<u32>() {",
        "        Some((name, id)) => match id.parse::<u32>() {",
        W1,
    ),
    Mutation(
        "X3b", CX,
        "            Err(_) => DemangledName { name: trimmed.to_string(), local_id: None, internal },",
        "            Err(_) => DemangledName { name: name.to_string(), local_id: None, internal },",
        W1,
    ),
    # --- filtering ---------------------------------------------------------
    Mutation(
        "X4", CX,
        "    if demangled.internal {\n        return None;\n    }",
        "    // mutated: nothing is filtered",
        W6,
    ),
    Mutation(
        "X5", CX,
        "    bindings.iter().filter(|b| demangle(&b.variable).internal).count()",
        "    0",
        W6,
    ),
    # --- order -------------------------------------------------------------
    Mutation(
        "X6", CX,
        "    for snapshot in &model.snapshots {",
        "    let mut ordered: Vec<&VenirSnapshot> = model.snapshots.iter().collect();\n"
        "    ordered.sort_by(|a, b| a.snapshot_id.cmp(&b.snapshot_id));\n"
        "    for snapshot in ordered {",
        W2,
    ),
    # --- the gate ----------------------------------------------------------
    Mutation(
        "X7", CX,
        "    if !model.is_populated() {\n        return None;\n    }",
        "    // mutated: an empty model still yields a trace",
        W4,
    ),
    Mutation(
        "X8", CX,
        "        !self.parameters.is_empty() || self.snapshots.iter().any(|s| !s.bindings.is_empty())",
        "        true",
        W4,
    ),
    # --- values ------------------------------------------------------------
    Mutation(
        "X9", CX,
        "        value: venir.value.clone(),",
        "        value: venir.constant.clone(),",
        W3,
    ),
    Mutation(
        "X10", CX,
        "        local_id: demangled.local_id,",
        "        local_id: None,",
        W3,
    ),
    # --- the violation -----------------------------------------------------
    Mutation(
        "X11", CX,
        "    steps.push(CounterexampleStep {\n        index: steps.len(),\n        kind: StepKind::Violation,",
        "    #[allow(unreachable_code)]\n    steps.push(CounterexampleStep {\n        index: steps.len(),\n        kind: StepKind::Assignment,",
        W7,
    ),
    Mutation(
        "X12", CX,
        "        ObligationKind::Assertion\n    } else {",
        "        ObligationKind::Other\n    } else {",
        W7,
    ),
    # --- honesty -----------------------------------------------------------
    Mutation(
        "X13", CX,
        "        is_recorded_execution: false,",
        "        is_recorded_execution: true,",
        W5,
    ),
    Mutation(
        "X14", CX,
        "    let (status, absent_reason) = if filtered == 0 {",
        "    let (status, absent_reason) = if true {",
        W6,
    ),
    # --- attaching a trace to a finding ------------------------------------
    Mutation(
        "X15", EMIT,
        "        location: finding.location.clone(),",
        "        location: None,",
        W8,
    ),
    Mutation(
        "X16", EMIT,
        "        let finding = self.findings.iter().find(|f| f.id == finding_id)?;",
        "        let finding = self.findings.first()?;",
        W8,
    ),
    # --- attaching a model to its error ------------------------------------
    Mutation(
        "X17", COMM,
        "                    if matches!(other, SmtOutput::Error(_)) { pending_model.take() } else { None };",
        "                    if matches!(other, SmtOutput::Error(_)) { pending_model.clone() } else { None };",
        P1,
    ),
    Mutation(
        "X18", COMM,
        "                let model =\n"
        "                    if matches!(other, SmtOutput::Error(_)) { pending_model.take() } else { None };",
        "                let model = pending_model.take();",
        P2,
    ),
    Mutation(
        "X19", COMM,
        "                pending_model = Some(block.model);",
        "                if pending_model.is_none() {\n"
        "                    pending_model = Some(block.model);\n"
        "                }",
        P3,
    ),
]

DECLARED_SURVIVORS = [
    Mutation(
        "S1", CX,
        "            location: None,\n"
        "            description: format!(\"at program point `{}`\", snapshot.snapshot_id),",
        "            location: obligation.location.clone(),\n"
        "            description: format!(\"at program point `{}`\", snapshot.snapshot_id),",
        killer="",
        why="Giving every assignment step the obligation's own location would be "
            "wrong -- the values were produced elsewhere -- but no check can tell, "
            "because nothing on this side of the `venir` boundary knows where a "
            "program point is. The snapshot-to-span map is `SnapPos`, built in "
            "`vir`/`rust_verify`; until it crosses, `None` is the only honest "
            "answer and the only checkable one. Killing this needs a located "
            "snapshot, which is the next change on the producer side.",
    ),
]

TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)")
CHECKS = [W1, W2, W3, W4, W5, W6, W7, W8, W9, P1, P2, P3]


def matches(reported: str, killer: str) -> bool:
    """`cargo test` prints module paths; the table names the check."""
    return reported == killer or reported.endswith("::" + killer)


@dataclass
class RunResult:
    rc: int
    passed: list = field(default_factory=list)
    failed: list = field(default_factory=list)

    @property
    def total(self):
        return len(self.passed) + len(self.failed)


def run_suite() -> RunResult:
    proc = subprocess.run(
        ["cargo", "test", "-p", "formal_verification", "--lib", "--", *CHECKS],
        cwd=ROOT, capture_output=True, text=True, timeout=3600,
    )
    out = proc.stdout + proc.stderr
    res = RunResult(rc=proc.returncode)
    for line in out.splitlines():
        m = TEST_LINE.match(line.strip())
        if m:
            (res.passed if m.group(2) == "ok" else res.failed).append(m.group(1))
    if res.total == 0:
        print("---- suite produced no test result lines; last 40 lines follow ----")
        print("\n".join(out.splitlines()[-40:]))
    return res


def apply(mut: Mutation) -> str:
    path = ROOT / mut.path
    original = path.read_text()
    if original.count(mut.find) != 1:
        raise SystemExit(
            f"{mut.id}: pattern occurs {original.count(mut.find)} times in {mut.path}, "
            f"expected exactly 1. The mutation table has drifted from the source."
        )
    path.write_text(original.replace(mut.find, mut.replace))
    return original


def main() -> int:
    print("== control ==")
    control = run_suite()
    if control.failed or control.total == 0:
        print(f"CONTROL IS NOT GREEN: rc={control.rc} failed={control.failed}")
        return 1
    if control.total != len(CHECKS):
        print(f"CONTROL RAN {control.total} CHECKS, EXPECTED {len(CHECKS)}: {control.passed}")
        return 1
    print(f"control: rc={control.rc}, {control.total} checks, 0 failures\n")

    problems = 0
    for mut in MUTATIONS + DECLARED_SURVIVORS:
        original = apply(mut)
        try:
            res = run_suite()
        finally:
            (ROOT / mut.path).write_text(original)
        declared = mut in DECLARED_SURVIVORS
        if res.total == 0:
            verdict, note = "HARNESS-ERROR", "suite produced no results"
            problems += 1
        elif declared and res.failed:
            verdict, note = "NO-LONGER-A-SURVIVOR", f"now killed by {', '.join(res.failed)}"
            problems += 1
        elif declared:
            verdict, note = "survived (declared)", mut.why
        elif not res.failed:
            verdict, note = "SURVIVED", "no check noticed"
            problems += 1
        elif any(matches(f, mut.killer) for f in res.failed):
            others = [f for f in res.failed if not matches(f, mut.killer)]
            verdict = "killed"
            note = mut.killer + (f" (+{len(others)} more)" if others else "")
        else:
            verdict, note = "MISDIRECTED", f"died in {', '.join(res.failed)}, not {mut.killer}"
            problems += 1
        print(f"{mut.id:<5} {verdict:<20} {note}")

    killed = "killed"
    print(f"\n{problems} problems")
    return 0 if problems == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
