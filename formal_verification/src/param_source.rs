//! Per-parameter source information for monomorphised functions.
//!
//! Until Noir `v1.0.0-beta.19`, `monomorphization::ast::Function` carried a `func_sig:
//! FunctionSignature` — a copy of the HIR-level `(Vec<Param>, Option<Type>)` — and Verno
//! read two things out of it that the monomorphised AST does not otherwise record:
//!
//! 1. the source [`Location`] of each parameter, used to build the VIR span attached to
//!    the parameter (`vir_gen::function::get_function_params`); and
//! 2. whether the parameter was written `mut` in the source, used to decide where to
//!    insert the `let mut` rebinding that `lowering::mut_args` introduces.
//!
//! `FunctionSignature`, `Function::func_sig`, `Program::function_signatures` and
//! `Program::main_function_signature` were all removed upstream in
//! <https://github.com/noir-lang/noir/pull/11217> (`v1.0.0-beta.19`).
//!
//! Both facts are still available, but only on the HIR side, from
//! `NodeInterner::function_meta(hir_func_id).parameters`. Verno drives the `Monomorphizer`
//! by hand and therefore already maintains a map from monomorphised
//! [`FuncId`](noirc_frontend::monomorphization::ast::FuncId) back to
//! [`node_interner::FuncId`], so the information is collected there — while the interner
//! is still in scope — and carried alongside the `Program` through the lowering passes and
//! into VIR generation.
//!
//! Note that (2) is *also* recorded directly on the monomorphised parameter tuple
//! (`Parameters.1`), which is what `mut_args` uses to decide *which* parameters to rebind.
//! The HIR pattern is only consulted for the location.

use std::collections::HashMap;

use noirc_errors::Location;
use noirc_frontend::hir_def::stmt::HirPattern;
use noirc_frontend::monomorphization::ast::FuncId;
use noirc_frontend::node_interner::{self, NodeInterner};

/// What Verno used to read out of one entry of `Function::func_sig.0`.
#[derive(Debug, Clone, Copy)]
pub struct ParamSourceInfo {
    /// Source location of the parameter's pattern.
    pub location: Location,
    /// True when the parameter was declared `mut` in the source, i.e. its HIR pattern was
    /// a [`HirPattern::Mutable`].
    pub declared_mut: bool,
}

/// Per-function parameter source information, keyed by *monomorphised* function id.
pub type ParamSources = HashMap<FuncId, Vec<ParamSourceInfo>>;

/// Reads the parameter source information for one HIR function out of the interner.
pub fn collect_param_sources(
    interner: &NodeInterner,
    hir_func_id: &node_interner::FuncId,
) -> Vec<ParamSourceInfo> {
    interner
        .function_meta(hir_func_id)
        .parameters
        .0
        .iter()
        .map(|(hir_pattern, ..)| ParamSourceInfo {
            location: hir_pattern.location(),
            declared_mut: matches!(hir_pattern, HirPattern::Mutable(..)),
        })
        .collect()
}

/// Looks up the source information for `func_id`, padding or truncating to `param_count`.
///
/// A monomorphised function has no entry when Verno never learned its HIR id — the
/// `Monomorphizer`'s queue is the only place that mapping is observable, so a function
/// reached by a path Verno does not watch will be missing. Losing a location degrades a
/// diagnostic span; it must not drop a parameter, hence the explicit padding rather than a
/// `zip`, which would silently shorten the parameter list.
pub fn sources_for(
    sources: &ParamSources,
    func_id: FuncId,
    param_count: usize,
) -> Vec<Option<ParamSourceInfo>> {
    let known = sources.get(&func_id);
    (0..param_count).map(|index| known.and_then(|infos| infos.get(index)).copied()).collect()
}

/// The source location of each parameter, or `None` where it is not known.
pub fn locations_for(
    sources: &ParamSources,
    func_id: FuncId,
    param_count: usize,
) -> Vec<Option<Location>> {
    sources_for(sources, func_id, param_count)
        .into_iter()
        .map(|info| info.map(|info| info.location))
        .collect()
}

/// The source location of each parameter that was *declared* `mut`, and `None` for the
/// rest.
///
/// This reproduces exactly what `func_sig` used to give `lowering::mut_args`: it read the
/// location out of the `HirPattern::Mutable` wrapper, so a parameter without that wrapper
/// contributed `None` even if the monomorphised parameter tuple said it was mutable.
pub fn mut_locations_for(
    sources: &ParamSources,
    func_id: FuncId,
    param_count: usize,
) -> Vec<Option<Location>> {
    sources_for(sources, func_id, param_count)
        .into_iter()
        .map(|info| info.filter(|info| info.declared_mut).map(|info| info.location))
        .collect()
}
