# Machine-readable reports

Every `verno formal-verify` run writes a JSON report describing what it found:

```
<target-dir>/verno-report.json
```

It is written on **every** run, without being asked, including the runs that
end in an error — a run that failed is precisely the run whose report is worth
having. `--report-json <path>` puts it somewhere else; `--no-report-json`
suppresses it.

## Why it is written by default

The report exists so an editor can show a verification result without scraping
Verno's terminal output. The editor that consumes it first — CodeTracer —
launches whatever command a project declares in its own `tasks.json` and adds
nothing to it, by design ([Noir-Studio §9.3][noir-studio]: *"we surface what a
project declares and invent no manifest of our own"*). It therefore cannot
append `--report-json` for you. A report only reaches it if Verno writes one
unprompted, at a place the consumer knows to look.

If nothing reads the file, nothing breaks: it is a small JSON document in the
target directory, which `nargo clean` removes along with everything else there.

## What it contains

```jsonc
{
  "schema": "codetracer.verification/v1",
  "producer": { "name": "verno", "version": "...", "language_release": "v1.0.0-beta.26" },
  "run": { "started_at_unix_ms", "workspace_root", "package", "argv",
           "solver": { "invoked", "name", "unavailable_reason" } },
  "outcome": "proved | not-proved | timed-out | unsupported | no-solver | pipeline-error",
  "outcome_detail": "one line saying why",
  "trust": { "class": "...", "reason": "...", "oracle_footprint": { ... } },
  "findings": [ { "kind", "message", "detail", "construct", "location", "trust" } ],
  "counterexample_traces": [ ... ],
  "goal_trees": [ ... ],
  "solver_queries": [ ... ],
  "source_map": { "files": [ ... ] }
}
```

Three things about it are worth knowing before you use it.

**The outcome is one of six, and only one of them is a failed proof.** They are
the same six [`scripts/run-corpus.py`](https://github.com/blocksense-network/verno/blob/main/scripts/run-corpus.py)
reports, spelled identically. An unsupported construct
(see [Limitations](./limitations.md)) is `unsupported` and carries a
`limitation` finding naming the construct; it is never a failed obligation, and
the format does not allow it to be one.

**Every part of the report says how much it can be trusted.** `trust.class` is
one of `checked-by-trusted-core`, `proof-reconstructed`, `solver-oracle` or
`diagnostic-only`, and it is required on the report and on every finding,
counterexample, goal tree and query inside it. Verno emits `solver-oracle` only
for a `proved` verdict and only with an oracle footprint saying what was
trusted — everything else is `diagnostic-only`, **including a failed
obligation**: with quantifiers and a resource limit, "the solver did not
discharge this" is not a proof that your program is wrong.

**A wall-clock timeout never produces a report.** Verno is killed before it can
write one, so a consumer that finds a stale file at the path must reject it —
which is why `run.started_at_unix_ms` is there.

## What is not in it yet

`counterexample_traces` is present but its `model` is `unavailable`, with the
reason stated in the document itself. That is not a gap in this format and not
a platform limitation: `venir` returns no counterexample model. Its output
surface is four JSON message shapes carrying five strings between them, and the
model that the underlying `air` layer produces for a satisfiable query is
discarded before `venir`'s reporter sees it. The same goes for the SMT-LIB
query text, the unsat core and the solver statistics.

The format carries the slots so that a `venir` which forwards a model needs no
schema change on either side.

## The contract, and testing against it

The full contract — field by field, with the rules a consumer must refuse a
document for — is
[Verification-Payload-Contract-v1.md][contract] in the CodeTracer specs.

`conformance/codetracer-payload/` in this repository is a corpus both sides
test against: seven documents a conforming consumer must accept, ten it must
refuse, and a `PROVENANCE.md` saying which were produced by a real run and
which were written by hand. `manifest.json` lists a SHA-256 for each and is
byte-identical to the copy CodeTracer holds, so a fixture edited on one side
and not the other fails on both.

[noir-studio]: https://github.com/metacraft-labs/codetracer-specs/blob/main/Planned-Features/Noir-Studio.md
[contract]: https://github.com/metacraft-labs/codetracer-specs/blob/main/Planned-Features/Verification-Payload-Contract-v1.md
