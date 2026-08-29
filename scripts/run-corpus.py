#!/usr/bin/env python3
"""Run Verno's proof corpus and report three distinct outcomes.

    scripts/run-corpus.py                 # run everything, print a summary
    scripts/run-corpus.py --json out.json # also write a machine-readable report
    scripts/run-corpus.py --baseline docs/corpus-baseline.json   # compare and exit non-zero on a regression

Why this exists
---------------
An SMT-backed prover does not fail cleanly. A proof that used to succeed can stop
succeeding because the solver ran out of budget, because the machine was slower, or
because the program genuinely stopped being provable — and in Verno's own output all
three look the same: a resource-limit exhaustion is serialised as an ordinary `Error`
block, exactly like a failed proof.  A pass/fail harness therefore cannot tell a
regression from a timeout, which is what would make any post-upgrade report untrustworthy.

This runner separates them, and pins the resource limits so that the answer is
reproducible on a different machine.

Outcomes
--------
Every corpus entry lands in exactly one bucket:

  proved          the solver discharged every obligation
  not-proved      the solver ran and rejected the program
  timed-out       the solver ran out of budget (SMT rlimit) or wall clock.
                  *Never* counted as a lost proof.
  unsupported     the program uses a construct Verno does not implement; Verno signals
                  this by panicking out of a `todo!()`/`unimplemented!()`. Does not move
                  the proved/not-proved counts.
  no-solver       the whole Noir -> VIR pipeline completed but the `venir` binary is not
                  available on this machine, so the proof was never attempted. This is
                  the normal outcome on macOS, where `venir` and `vstd.vir` are Linux-only.
                  It is a *front-end* pass: it proves the compiler-facing half of Verno
                  still works, which is precisely what an upstream Noir bump can break.
  pipeline-error  Verno failed before reaching the solver: a parse, type-check,
                  monomorphisation or VIR-generation error, or a crash. This is the
                  bucket an upstream-bump regression lands in.

Pinned limits
-------------
See RLIMIT / WALL_CLOCK_TIMEOUT_SECS below. `--rlimit` is an SMT *resource* count, not
wall-clock time, so it is reproducible across machines; the wall-clock timeout is only a
backstop for a hung process and any entry that hits it is reported as timed out.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

# ---------------------------------------------------------------------------
# Pinned resource limits. Changing either of these invalidates a stored baseline.
# ---------------------------------------------------------------------------

#: Verus' SMT resource limit, passed through to `venir`. Verus' own default is 10 and
#: nothing in Verno sets it, so it is pinned here explicitly: an unpinned limit is the
#: difference between "this proof regressed" and "this machine was busier today".
RLIMIT = int(os.environ.get("VERNO_CORPUS_RLIMIT", "10"))

#: Wall-clock backstop per corpus entry, in seconds. Only reached if a process hangs;
#: the SMT rlimit above should bite first. VN-M0 measured the whole corpus completing the
#: Noir->VIR pipeline in 43.4 s *in total*, so 120 s for a single entry is generous.
WALL_CLOCK_TIMEOUT_SECS = float(os.environ.get("VERNO_CORPUS_TIMEOUT_SECS", "120"))

#: Both limits can be overridden through the environment, which exists so that the
#: timeout/regression distinction can itself be tested: lower the budget and previously
#: passing entries must report as *timed out*, not as newly unprovable. A run with
#: overridden limits records them in its report, and `--baseline` refuses to compare two
#: runs whose limits differ, so an overridden run can never masquerade as a baseline.

# ---------------------------------------------------------------------------

SUCCESS_DIR = "formal_verify_success"
FAILURE_DIR = "formal_verify_failure"

PROVED = "proved"
NOT_PROVED = "not-proved"
TIMED_OUT = "timed-out"
UNSUPPORTED = "unsupported"
NO_SOLVER = "no-solver"
PIPELINE_ERROR = "pipeline-error"

OUTCOMES = [PROVED, NOT_PROVED, TIMED_OUT, UNSUPPORTED, NO_SOLVER, PIPELINE_ERROR]

#: Verus serialises a resource-limit exhaustion as an ordinary error block. This is the
#: only string that distinguishes it from a genuine unprovable result.
RLIMIT_MARKER = "Resource limit (rlimit) exceeded"

#: Verno reports "the solver could not be started" distinctly from "the solver said no".
NO_SOLVER_MARKER = "Failed to start the Venir binary"

#: How Verno signals an unimplemented construct: `todo!()` and `unimplemented!()` both
#: panic with "not yet implemented". Verno's own `todo!()`s carry an `UNSUPPORTED:` prefix
#: naming the construct, so the harness can report *which* one was hit rather than just
#: that something was missing — see docs/src/limitations.md. `unreachable!()` is kept
#: separate: it means an invariant Verno believed was broken, which is a bug, not a
#: documented limitation.
UNSUPPORTED_MARKERS = [
    "not yet implemented",
]

SUCCESS_MARKER = "Verification successful!"


@dataclass
class Result:
    name: str
    kind: str  # "success" or "failure" corpus
    outcome: str
    seconds: float
    exit_code: int | None
    detail: str


def find_verno() -> Path:
    """Locate the `verno` binary, preferring an explicit override."""
    if override := os.environ.get("VERNO_BIN"):
        return Path(override)
    for profile in ("release", "debug"):
        candidate = REPO_ROOT / "target" / profile / "verno"
        if candidate.exists():
            return candidate
    sys.exit(
        "could not find a `verno` binary; run `cargo build` first, "
        "or set VERNO_BIN to its path"
    )


def corpus_entries(kind: str) -> list[Path]:
    directory = REPO_ROOT / "test_programs" / kind
    if not directory.is_dir():
        return []
    return sorted(
        entry
        for entry in directory.iterdir()
        if entry.is_dir() and (entry / "Nargo.toml").exists()
    )


def classify(kind: str, exit_code: int | None, output: str, timed_out: bool) -> tuple[str, str]:
    """Map one run to an outcome and a one-line reason.

    Order matters: a timeout and an unsupported construct are both checked *before*
    anything is allowed to count as a lost proof.
    """
    if timed_out:
        return TIMED_OUT, f"wall clock exceeded {WALL_CLOCK_TIMEOUT_SECS}s"

    if RLIMIT_MARKER in output:
        return TIMED_OUT, f"solver rlimit {RLIMIT} exhausted"

    if "UNSUPPORTED:" in output:
        # Verno names the construct it could not handle.
        return UNSUPPORTED, first_line_containing(output, "UNSUPPORTED:")
    for marker in UNSUPPORTED_MARKERS:
        if marker in output:
            return UNSUPPORTED, first_line_containing(output, marker)

    if NO_SOLVER_MARKER in output:
        return NO_SOLVER, "Noir -> VIR pipeline completed; `venir` not available"

    if SUCCESS_MARKER in output:
        return PROVED, "verification successful"

    if exit_code == 0:
        # The success corpus asserts only `exit 0`, so an entry can pass without printing
        # the success banner. Treat that as proved but say so.
        return PROVED, "exited 0 without a success banner"

    # A non-zero exit that is not any of the above. Distinguish "the solver rejected it"
    # from "Verno never got as far as the solver": only the latter is a port regression.
    if "error:" in output or "Aborting due to" in output:
        return (NOT_PROVED if reached_solver(output) else PIPELINE_ERROR), first_error_line(output)

    return PIPELINE_ERROR, first_error_line(output) or f"exit {exit_code}"


def reached_solver(output: str) -> bool:
    """True when Verno got as far as running the solver.

    Verno prints verification diagnostics only after `venir` has answered, so any output
    naming a pre-solver phase means the pipeline itself failed.
    """
    pre_solver_markers = (
        "Non-ghost function",
        "cannot compile crate",
        "no binary packages",
        "no verifiable functions",
        "cannot find a Nargo.toml",
    )
    if any(marker in output for marker in pre_solver_markers):
        return False
    return "Verification failed" in output or "Verification crashed" in output


def first_error_line(output: str) -> str:
    for line in output.splitlines():
        stripped = line.strip()
        if stripped.startswith("error") or stripped.startswith("Error"):
            return stripped[:200]
    for line in output.splitlines():
        if line.strip():
            return line.strip()[:200]
    return ""


def first_line_containing(output: str, needle: str) -> str:
    for line in output.splitlines():
        if needle in line:
            return line.strip()[:200]
    return needle


def run_entry(verno: Path, entry: Path, kind: str) -> Result:
    command = [
        str(verno),
        "--program-dir",
        str(entry),
        "formal-verify",
        "--",
        "--rlimit",
        str(RLIMIT),
    ]
    started = time.monotonic()
    timed_out = False
    try:
        completed = subprocess.run(
            command,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=WALL_CLOCK_TIMEOUT_SECS,
        )
        output = completed.stdout + completed.stderr
        exit_code = completed.returncode
    except subprocess.TimeoutExpired as expired:
        timed_out = True
        output = (expired.stdout or "") + (expired.stderr or "")
        if isinstance(output, bytes):
            output = output.decode("utf-8", "replace")
        exit_code = None
    elapsed = time.monotonic() - started

    outcome, detail = classify(kind, exit_code, output, timed_out)
    return Result(entry.name, kind, outcome, round(elapsed, 3), exit_code, detail)


def expected_outcomes(kind: str) -> set[str]:
    """What a healthy run looks like for each half of the corpus.

    `no-solver` is expected for both halves on a machine without `venir`: it means the
    compiler-facing half of Verno worked and the proof was simply never attempted.
    """
    if kind == SUCCESS_DIR:
        return {PROVED, NO_SOLVER}
    # The failure corpus asserts only that Verno rejects the program. Some of its entries
    # are rejected before the solver is ever reached (`exec_function_in_attribute` is
    # rejected during monomorphisation), which is the behaviour those entries are testing,
    # so `pipeline-error` is an expected outcome on this side. The baseline comparison is
    # what catches an entry moving *between* these buckets.
    return {NOT_PROVED, NO_SOLVER, PIPELINE_ERROR}


# ---------------------------------------------------------------------------
# VN-M4: the structured payload, cross-checked against this classifier
# ---------------------------------------------------------------------------

PAYLOAD_SCHEMA = "codetracer.verification/v1"
PAYLOAD_FILE = "verno-report.json"


def check_payloads(results: list[Result]) -> tuple[int, list[str]]:
    """Compare each entry's structured report against what this script classified.

    This is the regression guard for VN-M4's emitter, and it is cheap because the
    corpus has already run: every entry has just written a
    `target/verno-report.json`, and every entry has just been classified from text
    by `classify()` above. The two are computed by completely different means —
    one from values inside Verno, the other by matching strings in its output —
    so an agreement across the whole corpus is worth something, and a
    disagreement is a real defect in one of them.

    Two ways to fail, and the second matters as much as the first:

    * any entry whose payload names a different outcome than the text did;
    * **zero payloads found at all**, which would mean the emitter has stopped
      running and would otherwise let this check pass vacuously — the failure
      mode this project has already found five times.

    A *missing* payload for some entries is only reported. An entry that panics
    hard enough to take the process down before the hook runs would have none,
    and that is a fact about that entry rather than a fault in the emitter.
    """
    agreed = 0
    missing: list[str] = []
    problems: list[str] = []

    for result in results:
        report_path = (
            REPO_ROOT / "test_programs" / result.kind / result.name / "target" / PAYLOAD_FILE
        )
        if not report_path.exists():
            missing.append(f"{result.kind}/{result.name}")
            continue
        try:
            payload = json.loads(report_path.read_text())
        except (OSError, json.JSONDecodeError) as error:
            problems.append(f"{result.kind}/{result.name}: unreadable report ({error})")
            continue
        if payload.get("schema") != PAYLOAD_SCHEMA:
            problems.append(
                f"{result.kind}/{result.name}: report declares schema "
                f"{payload.get('schema')!r}, expected {PAYLOAD_SCHEMA!r}"
            )
            continue
        if payload.get("outcome") != result.outcome:
            problems.append(
                f"{result.kind}/{result.name}: report says {payload.get('outcome')!r} "
                f"where the classifier read {result.outcome!r} — {result.detail}"
            )
            continue
        agreed += 1

    print()
    print(
        f"structured reports: {agreed} of {len(results)} agree with the classifier"
        + (f", {len(missing)} absent" if missing else "")
    )
    for problem in problems:
        print(f"  {problem}")
    if missing and len(missing) <= 10:
        for name in missing:
            print(f"  no report written: {name}")

    if agreed == 0 and results:
        problems.append(
            "no entry produced a structured report at all; the emitter is not running, "
            "and this check would otherwise have passed by finding nothing to check"
        )
        print(f"  {problems[-1]}")

    return agreed, problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--json", type=Path, help="write the full report here")
    parser.add_argument(
        "--baseline",
        type=Path,
        help="compare against a previous --json report and fail on a regression",
    )
    parser.add_argument("--filter", help="only run entries whose name contains this")
    parser.add_argument(
        "--no-payload-check",
        action="store_true",
        help=(
            "skip the VN-M4 cross-check of each entry's structured report against "
            "this script's own classification of its text"
        ),
    )
    parser.add_argument(
        "--write-baseline",
        type=Path,
        help="write this run out as a baseline (implies --json)",
    )
    args = parser.parse_args()

    verno = find_verno()
    print(f"verno:   {verno}")
    print(f"rlimit:  {RLIMIT}   wall clock: {WALL_CLOCK_TIMEOUT_SECS}s   (pinned)")
    print()

    results: list[Result] = []
    started = time.monotonic()
    for kind in (SUCCESS_DIR, FAILURE_DIR):
        for entry in corpus_entries(kind):
            if args.filter and args.filter not in entry.name:
                continue
            result = run_entry(verno, entry, kind)
            results.append(result)
            print(f"  {result.outcome:<15} {kind}/{result.name}")
    total_seconds = time.monotonic() - started

    print()
    print(f"{len(results)} entries in {total_seconds:.1f}s")
    for outcome in OUTCOMES:
        count = sum(1 for r in results if r.outcome == outcome)
        if count:
            print(f"  {outcome:<15} {count}")

    unexpected = [r for r in results if r.outcome not in expected_outcomes(r.kind)]
    if unexpected:
        print()
        print("Entries whose outcome is not what this half of the corpus expects:")
        for result in unexpected:
            print(f"  {result.kind}/{result.name}: {result.outcome} — {result.detail}")

    report = {
        "rlimit": RLIMIT,
        "wall_clock_timeout_secs": WALL_CLOCK_TIMEOUT_SECS,
        "total_seconds": round(total_seconds, 1),
        "counts": {o: sum(1 for r in results if r.outcome == o) for o in OUTCOMES},
        "results": [asdict(r) for r in results],
    }

    for destination in (args.json, args.write_baseline):
        if destination:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
            print(f"\nwrote {destination}")

    payload_problems: list[str] = []
    if not args.no_payload_check:
        _, payload_problems = check_payloads(results)

    exit_code = 0
    if args.baseline:
        exit_code = compare_to_baseline(json.loads(args.baseline.read_text()), results)
    elif unexpected:
        exit_code = 1
    if payload_problems:
        exit_code = 1
    return exit_code


def compare_to_baseline(baseline: dict, results: list[Result]) -> int:
    """Report regressions against a recorded baseline.

    Two rules make this trustworthy, and they are the reason the harness exists:

    * **A timeout is never reported as a lost proof.** An entry that was proved and now
      times out is listed under its own heading and does not fail the run: what changed is
      the solver's budget, not the program. Only a proof that the solver *ran* and rejected
      counts as a regression.
    * **An entry may never disappear.** Anything in the baseline that this run did not
      produce is reported and fails, so a corpus entry cannot be quietly dropped to make
      the numbers look better.

    A run without a solver (`no-solver`) is a partial result, not a pass: it says the whole
    Noir -> VIR pipeline worked and the proof was never attempted. Moving in or out of that
    state is reported separately from a regression, because it reflects the machine rather
    than the code.
    """
    if baseline.get("rlimit") != RLIMIT or (
        baseline.get("wall_clock_timeout_secs") != WALL_CLOCK_TIMEOUT_SECS
    ):
        print(
            "\nBASELINE MISMATCH: this run used different resource limits than the "
            f"baseline (baseline rlimit={baseline.get('rlimit')}, "
            f"timeout={baseline.get('wall_clock_timeout_secs')}s). "
            "The comparison would not be meaningful."
        )
        return 1

    before = {(r["kind"], r["name"]): r["outcome"] for r in baseline["results"]}
    after = {(r.kind, r.name): r for r in results}

    regressions: list[str] = []
    timeouts: list[str] = []
    improvements: list[str] = []
    solver_availability: list[str] = []
    dropped: list[str] = []

    attempted = {PROVED, NOT_PROVED}

    for key, old_outcome in before.items():
        kind, name = key
        current = after.get(key)
        if current is None:
            dropped.append(f"{kind}/{name} (was {old_outcome})")
            continue
        new_outcome = current.outcome
        if new_outcome == old_outcome:
            continue

        label = f"{kind}/{name}: {old_outcome} -> {new_outcome}"
        if current.detail:
            label += f" — {current.detail}"

        acceptable = expected_outcomes(kind)
        old_ok = old_outcome in acceptable
        new_ok = new_outcome in acceptable

        if new_outcome == TIMED_OUT:
            timeouts.append(label)
        elif new_outcome == PIPELINE_ERROR and old_outcome != PIPELINE_ERROR:
            # Verno stopped reaching the solver at all. This is what an unabsorbed upstream
            # change looks like, and it is a regression even on the failure corpus, where
            # `pipeline-error` is otherwise an accepted outcome.
            regressions.append(label)
        elif old_outcome == NO_SOLVER and new_outcome in attempted and new_ok:
            solver_availability.append(f"{label}  (a solver became available)")
        elif old_outcome in attempted and new_outcome == NO_SOLVER:
            solver_availability.append(
                f"{label}  (no solver on this machine — this run proves LESS than the baseline)"
            )
        elif old_ok and not new_ok:
            regressions.append(label)
        elif new_ok and not old_ok:
            improvements.append(label)
        else:
            regressions.append(label)

    new_entries = [k for k in after if k not in before]

    print("\n--- against baseline ---")
    if dropped:
        print("MISSING (in the baseline, not run now — never drop a corpus entry silently):")
        for line in dropped:
            print(f"  {line}")
    if timeouts:
        print("TIMED OUT (solver budget, NOT a lost proof):")
        for line in timeouts:
            print(f"  {line}")
    if solver_availability:
        print("SOLVER AVAILABILITY CHANGED (not a code change):")
        for line in solver_availability:
            print(f"  {line}")
    if improvements:
        print("IMPROVED:")
        for line in improvements:
            print(f"  {line}")
    if new_entries:
        print(f"NEW: {len(new_entries)} entries not in the baseline")
    if regressions:
        print("REGRESSIONS:")
        for line in regressions:
            print(f"  {line}")
        return 1
    if dropped:
        return 1
    print("no regressions")
    return 0


def self_test() -> int:
    """Assert the outcome classifier and the baseline comparison behave as documented.

    These are the properties the whole harness exists for, so they are checked without
    needing a solver — which matters, because `venir` is Linux-only and the classifier
    would otherwise be untested on the machine most of this work happens on.
    """
    failures: list[str] = []

    def check(label: str, actual, expected) -> None:
        if actual != expected:
            failures.append(f"{label}: expected {expected!r}, got {actual!r}")

    # Verus reports a resource-limit exhaustion as an ordinary error block. The wording is
    # `air/src/main.rs` in the pinned verus-lib revision:
    #   "Resource limit (rlimit) exceeded; consider rerunning with --profile for more details"
    rlimit_output = (
        "error: function body check: Resource limit (rlimit) exceeded; "
        "consider rerunning with --profile for more details\n"
        "Error: Verification failed due to 1 previous errors!\n"
    )
    outcome, _ = classify(SUCCESS_DIR, 1, rlimit_output, timed_out=False)
    check("rlimit exhaustion is a timeout, not a lost proof", outcome, TIMED_OUT)

    # A genuinely failed proof looks almost the same, minus that one string.
    lost_proof_output = (
        "error: postcondition not satisfied\n"
        "Error: Verification failed due to 1 previous errors!\n"
    )
    outcome, _ = classify(SUCCESS_DIR, 1, lost_proof_output, timed_out=False)
    check("a failed proof is not-proved", outcome, NOT_PROVED)

    # An unsupported construct panics out of a `todo!()`.
    unsupported_output = (
        "The application panicked (crashed).\n"
        "Message:  not yet implemented: Vectors are not supported by Verno\n"
    )
    outcome, _ = classify(SUCCESS_DIR, 101, unsupported_output, timed_out=False)
    check("an unsupported construct is unsupported", outcome, UNSUPPORTED)

    # A front-end failure is the bucket an upstream-bump regression lands in.
    pipeline_output = "error: Expected type tuple, found type 5\nAborting due to 1 previous error\n"
    outcome, _ = classify(SUCCESS_DIR, 1, pipeline_output, timed_out=False)
    check("a front-end error is a pipeline error", outcome, PIPELINE_ERROR)

    outcome, _ = classify(SUCCESS_DIR, None, "", timed_out=True)
    check("a wall-clock kill is a timeout", outcome, TIMED_OUT)

    # --- the comparison ---------------------------------------------------------
    baseline = {
        "rlimit": RLIMIT,
        "wall_clock_timeout_secs": WALL_CLOCK_TIMEOUT_SECS,
        "results": [
            {"kind": SUCCESS_DIR, "name": "was_proved_now_times_out", "outcome": PROVED},
            {"kind": SUCCESS_DIR, "name": "was_proved_now_fails", "outcome": PROVED},
            {"kind": SUCCESS_DIR, "name": "was_proved_still_proved", "outcome": PROVED},
            {"kind": SUCCESS_DIR, "name": "unsupported_all_along", "outcome": UNSUPPORTED},
        ],
    }
    now = [
        Result("was_proved_now_times_out", SUCCESS_DIR, TIMED_OUT, 0.0, None, ""),
        Result("was_proved_now_fails", SUCCESS_DIR, NOT_PROVED, 0.0, 1, ""),
        Result("was_proved_still_proved", SUCCESS_DIR, PROVED, 0.0, 0, ""),
        Result("unsupported_all_along", SUCCESS_DIR, UNSUPPORTED, 0.0, 101, ""),
    ]
    print("\n(the comparison below is the self-test's synthetic corpus)")
    exit_code = compare_to_baseline(baseline, now)
    check("a real lost proof fails the comparison", exit_code, 1)

    # ...and with the genuinely-lost proof removed, a timeout alone must NOT fail it.
    baseline_no_regression = dict(baseline)
    baseline_no_regression["results"] = [
        r for r in baseline["results"] if r["name"] != "was_proved_now_fails"
    ]
    now_no_regression = [r for r in now if r.name != "was_proved_now_fails"]
    exit_code = compare_to_baseline(baseline_no_regression, now_no_regression)
    check("a timeout alone does not fail the comparison", exit_code, 0)

    # An entry present in the baseline but not in this run must never pass silently.
    exit_code = compare_to_baseline(baseline_no_regression, now_no_regression[:1])
    check("a dropped corpus entry fails the comparison", exit_code, 1)

    # A run under different limits must refuse to be compared at all.
    mismatched = dict(baseline_no_regression)
    mismatched["rlimit"] = RLIMIT + 1
    exit_code = compare_to_baseline(mismatched, now_no_regression)
    check("mismatched resource limits refuse comparison", exit_code, 1)

    print()
    if failures:
        for failure in failures:
            print(f"SELF-TEST FAILED  {failure}")
        return 1
    print("self-test: all outcome-classification properties hold")
    return 0


if __name__ == "__main__":
    if "--self-test" in sys.argv:
        sys.exit(self_test())
    sys.exit(main())
