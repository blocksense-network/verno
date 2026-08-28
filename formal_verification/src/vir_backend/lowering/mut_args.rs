//! Verus performs a transformation on function parameters where mutable arguments are
//! converted into immutable ones, and a `let mut` binding is inserted at the beginning
//! of the function body. To stay consistent with this behavior, we apply the same
//! transformation during our monomorphized AST passes.
//!
//! Specifically, the function:
//! ```
//! fn foo(mut x: T) {
//!     ...
//! }
//! ```
//! is transformed into:
//! ```
//! fn foo(x: T) {
//!     let mut x = x;
//!     ...
//! }
//! ```
//!
//! In short, `mut` is removed from the parameter list, and a mutable shadowing
//! `let` binding is inserted at the top of the function body.

use noirc_frontend::monomorphization::ast::{
    Definition, Expression, Function, Ident, IdentId, Let, Program,
};

use crate::param_source::{ParamSources, mut_locations_for};

pub fn demut_parameters(program: &mut Program, param_sources: &ParamSources) {
    program.functions.iter_mut().for_each(|function| {
        demut_parameters_inner(function, param_sources);
    });
}

fn demut_parameters_inner(function: &mut Function, param_sources: &ParamSources) {
    insert_let_mut_exprs(function, param_sources);
    convert_mut_params_to_non_mut(function)
}

fn insert_let_mut_exprs(function: &mut Function, param_sources: &ParamSources) {
    // Which parameters are rebound is read below from `parameters` itself (`param.1`), as
    // it always was; only the source location came from `func_sig`, which upstream removed
    // in noir-lang/noir#11217 (`v1.0.0-beta.19`). It is now carried alongside the program —
    // see `crate::param_source` — and is supplied only for parameters whose HIR pattern was
    // a `HirPattern::Mutable`, which is exactly what `func_sig` used to yield here.
    let param_locations = mut_locations_for(param_sources, function.id, function.parameters.len());

    function
        .parameters
        .iter()
        .zip(param_locations)
        .filter(|(param, _)| param.1) // is mut
        // Get parameter's local id, name, type and location
        .map(|(param, location)| (param.0, param.2.clone(), param.3.clone(), location))
        .rev()
        .for_each(|(local_id, param_name, param_type, location)| {
            // Insert `let` expression at the start of the body's block
            if let Expression::Block(block) = &mut function.body {
                block.insert(
                    0,
                    Expression::Let(Let {
                        id: local_id,
                        mutable: true,
                        name: param_name.clone(),
                        expression: Box::new(Expression::Ident(Ident {
                            location,
                            definition: Definition::Local(local_id),
                            mutable: false,
                            name: param_name,
                            typ: param_type,
                            id: IdentId(local_id.0),
                        })),
                    }),
                );
            }
        });
}

fn convert_mut_params_to_non_mut(function: &mut Function) {
    function.parameters.iter_mut().for_each(|param| {
        param.1 = false; // Set mut to false
    });

    // The second half of this function used to strip the `HirPattern::Mutable` wrapper from
    // the matching `func_sig` entry, so that the two records of "is this parameter mut"
    // stayed in agreement. `func_sig` no longer exists (noir-lang/noir#11217), and the
    // monomorphised parameter tuple above is now the only such record, so there is nothing
    // left to keep in step.
}
