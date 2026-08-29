//! Emitting a payload for the run that ends in a panic.
//!
//! Two of Verno's six outcomes arrive as panics rather than as returned
//! errors, and they are the two it is most important not to confuse:
//!
//! * `todo!("UNSUPPORTED: <construct>")` — Verno does not implement a
//!   construct the program uses. **Not a failed proof**, and the payload must
//!   say so in a field rather than leave a consumer to recognise the panic
//!   text.
//! * `unreachable!()` — an invariant Verno relies on did not hold. A bug to be
//!   reported, deliberately kept out of the limitation bucket so an internal
//!   compiler error cannot hide as a documented limitation.
//!
//! A panic unwinds past every `?` in the command, so there is no return path
//! that could write the report. A panic *hook* has one, and it runs before the
//! default hook prints anything, so the process's stderr is unchanged — the
//! text tier sees exactly what it saw before this module existed.
//!
//! The hook writes only when [`arm`] has been called with somewhere to write.
//! A `verno` invocation that is not a verification run leaves it disarmed and
//! behaves as it always did.

use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};

use super::emit::{NOIR_RELEASE, now_unix_ms};
use super::{
    Finding, FindingKind, Outcome, Producer, ProofVisualizationSourceMap, RunInfo, SCHEMA_ID,
    SolverInfo, Trust, VerificationPayload,
};

/// The prefix every deliberate `todo!()` in the translator carries.
///
/// `docs/src/limitations.md` states the contract: "every entry below
/// corresponds to a specific place in the translator that refuses to continue,
/// and each of those places names its construct in the message it prints".
pub const UNSUPPORTED_PREFIX: &str = "UNSUPPORTED: ";

/// What `unreachable!()` panics with.
///
/// Matched *before* the generic `todo!()` marker so an ICE cannot be read as a
/// limitation.
pub const UNREACHABLE_MARKER: &str = "internal error: entered unreachable code";

/// What `todo!()`/`unimplemented!()` panic with, for the `todo!()`s that
/// predate the prefix discipline.
pub const UNIMPLEMENTED_MARKER: &str = "not yet implemented";

#[derive(Clone)]
struct Context {
    path: PathBuf,
    started_at_unix_ms: u64,
    workspace_root: String,
    package: Option<String>,
    entry_file: Option<String>,
    argv: Vec<String>,
}

fn slot() -> &'static Mutex<Option<Context>> {
    static SLOT: OnceLock<Mutex<Option<Context>>> = OnceLock::new();
    SLOT.get_or_init(|| Mutex::new(None))
}

/// Arm the hook. Installs it on first call.
#[allow(clippy::too_many_arguments)]
pub fn arm(
    path: PathBuf,
    started_at_unix_ms: u64,
    workspace_root: String,
    package: Option<String>,
    entry_file: Option<String>,
    argv: Vec<String>,
) {
    install();
    if let Ok(mut guard) = slot().lock() {
        *guard =
            Some(Context { path, started_at_unix_ms, workspace_root, package, entry_file, argv });
    }
}

/// Disarm the hook once the run has written its own report.
///
/// Without this, a panic *after* a successful verification — in cleanup, say —
/// would overwrite a real report with a pipeline error.
pub fn disarm() {
    if let Ok(mut guard) = slot().lock() {
        *guard = None;
    }
}

fn install() {
    static INSTALLED: OnceLock<()> = OnceLock::new();
    INSTALLED.get_or_init(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            let context = slot().lock().ok().and_then(|guard| guard.clone());
            if let Some(context) = context {
                let message = panic_message(info);
                let payload = payload_for_panic(&context, &message);
                // A failure to write must not shadow the panic itself, which
                // is the thing the developer needs to see.
                let _ = payload.write_to(&context.path);
            }
            previous(info);
        }));
    });
}

fn panic_message(info: &std::panic::PanicHookInfo<'_>) -> String {
    if let Some(text) = info.payload().downcast_ref::<&str>() {
        (*text).to_string()
    } else if let Some(text) = info.payload().downcast_ref::<String>() {
        text.clone()
    } else {
        String::new()
    }
}

/// The construct named after the `UNSUPPORTED:` prefix, or `None`.
pub fn unsupported_construct(message: &str) -> Option<String> {
    let position = message.find(UNSUPPORTED_PREFIX)?;
    let tail = &message[position + UNSUPPORTED_PREFIX.len()..];
    let named = tail.lines().next().unwrap_or("").trim();
    if named.is_empty() { None } else { Some(named.to_string()) }
}

/// Classify a panic message into an outcome.
///
/// The ordering is the one `run-corpus.py::classify` and CodeTracer's
/// `classifyVernoRun` both use, and it is the ordering that matters most:
/// `unreachable!()` is recognised **before** the generic `not yet implemented`
/// fallback, so an ICE lands in `pipeline-error` and never in `unsupported`.
pub fn classify_panic(message: &str) -> Outcome {
    if message.contains(UNSUPPORTED_PREFIX) {
        Outcome::Unsupported
    } else if message.contains(UNREACHABLE_MARKER) {
        Outcome::PipelineError
    } else if message.contains(UNIMPLEMENTED_MARKER) {
        Outcome::Unsupported
    } else {
        Outcome::PipelineError
    }
}

fn payload_for_panic(context: &Context, message: &str) -> VerificationPayload {
    let outcome = classify_panic(message);
    let construct = unsupported_construct(message);
    let finding = match outcome {
        Outcome::Unsupported => {
            let named = construct
                .clone()
                .unwrap_or_else(|| "a construct Verno does not implement".to_string());
            Finding {
                id: "f0".to_string(),
                kind: FindingKind::Limitation,
                message: format!("Verno does not support {named}"),
                detail: "This is a limitation of the verifier, not a failed proof. The \
                         program may well be correct; Verno cannot say either way."
                    .to_string(),
                // Never `None`: the contract requires a limitation to name its
                // construct, and the fallback above is a name.
                construct: Some(named),
                location: None,
                location_absent_reason: Some(
                    "Verno's `todo!()` panics carry a Rust source position, never a Noir \
                     one, so there is no line in the program to point at"
                        .to_string(),
                ),
                excerpt: message.to_string(),
                trust: Trust::diagnostic_only(
                    "the verifier stopped before the solver; nothing was proved or disproved",
                ),
            }
        }
        _ => Finding {
            id: "f0".to_string(),
            kind: FindingKind::PipelineError,
            message: "Verno failed before it could reach the solver.".to_string(),
            detail: if message.contains(UNREACHABLE_MARKER) {
                "An invariant Verno relies on did not hold. This is a bug in the verifier \
                 and should be reported; it is deliberately not classed as a limitation."
                    .to_string()
            } else {
                String::new()
            },
            construct: None,
            location: None,
            location_absent_reason: Some(
                "the panic carries a Rust source position, not a Noir one".to_string(),
            ),
            excerpt: message.to_string(),
            trust: Trust::diagnostic_only("the verifier failed; nothing was established"),
        },
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
            started_at_unix_ms: context.started_at_unix_ms,
            finished_at_unix_ms: now_unix_ms(),
            workspace_root: context.workspace_root.clone(),
            package: context.package.clone(),
            entry_file: context.entry_file.clone(),
            argv: context.argv.clone(),
            solver: SolverInfo {
                invoked: false,
                name: "venir".to_string(),
                unavailable_reason: Some("the run ended before the solver was started".to_string()),
            },
        },
        outcome,
        outcome_detail: message.lines().next().unwrap_or("").trim().to_string(),
        trust: Trust::diagnostic_only(
            "the run reports on the verifier rather than on the program; nothing was \
             established either way",
        ),
        findings: vec![finding],
        counterexample_traces: Vec::new(),
        goal_trees: Vec::new(),
        solver_queries: Vec::new(),
        source_map: ProofVisualizationSourceMap::default(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context {
            path: PathBuf::from("/dev/null"),
            started_at_unix_ms: 1,
            workspace_root: "/tmp/example".to_string(),
            package: Some("example".to_string()),
            entry_file: None,
            argv: vec!["verno".to_string()],
        }
    }

    #[test]
    fn an_unsupported_panic_names_its_construct_and_is_never_a_failed_proof() {
        let message = "not yet implemented: UNSUPPORTED: function types (lambdas, function values)";
        assert_eq!(classify_panic(message), Outcome::Unsupported);
        assert_eq!(
            unsupported_construct(message).as_deref(),
            Some("function types (lambdas, function values)")
        );
        let payload = payload_for_panic(&context(), message);
        assert_eq!(payload.findings[0].kind, FindingKind::Limitation);
        assert!(!payload.outcome.is_failed_proof());
        assert!(!payload.outcome.answers_correctness());
        assert!(payload.check().is_empty(), "{:?}", payload.check());
    }

    #[test]
    fn an_unreachable_panic_is_a_pipeline_error_so_an_ice_cannot_hide_as_a_limitation() {
        // `unreachable!()` also panics with a message the generic
        // `not yet implemented` fallback must not claim, which is why the
        // ordering in `classify_panic` is load-bearing rather than cosmetic.
        let message = "internal error: entered unreachable code: Arrays must be of type Primitive";
        assert_eq!(classify_panic(message), Outcome::PipelineError);
        let payload = payload_for_panic(&context(), message);
        assert_eq!(payload.findings[0].kind, FindingKind::PipelineError);
        assert!(payload.findings[0].construct.is_none());
        assert!(payload.check().is_empty(), "{:?}", payload.check());
    }

    #[test]
    fn a_panic_carrying_both_markers_classifies_as_a_limitation() {
        // The hostile input: an `unreachable!()` whose message happens to
        // quote an `UNSUPPORTED:` string. The prefix check runs first, so this
        // one *would* classify as a limitation — which is the same behaviour
        // the text tier has, deliberately, and the residual risk both sides
        // record. Pinned here so a change to either is visible in the other.
        let message = "internal error: entered unreachable code: saw UNSUPPORTED: string types";
        assert_eq!(classify_panic(message), Outcome::Unsupported);
    }

    #[test]
    fn a_bare_todo_still_produces_a_named_limitation() {
        // `docs/src/limitations.md` says every site names its construct, but a
        // `todo!()` added without the prefix must not produce a payload that
        // breaks the contract's "a limitation names its construct" rule.
        let message = "not yet implemented";
        assert_eq!(classify_panic(message), Outcome::Unsupported);
        assert!(unsupported_construct(message).is_none());
        let payload = payload_for_panic(&context(), message);
        assert!(payload.check().is_empty(), "{:?}", payload.check());
        assert_eq!(
            payload.findings[0].construct.as_deref(),
            Some("a construct Verno does not implement")
        );
    }

    #[test]
    fn an_unrecognised_panic_is_a_pipeline_error_and_never_an_answer_about_the_program() {
        let payload = payload_for_panic(&context(), "index out of bounds");
        assert_eq!(payload.outcome, Outcome::PipelineError);
        assert!(!payload.outcome.answers_correctness());
        assert!(payload.check().is_empty(), "{:?}", payload.check());
    }
}
