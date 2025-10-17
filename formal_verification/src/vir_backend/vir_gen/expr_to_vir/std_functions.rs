use std::{collections::BTreeMap, sync::Arc};

use noirc_errors::Location;
use noirc_frontend::monomorphization::ast::{Call, Expression, GlobalId, Type};
use vir::ast::{Expr, ExprX, LoopInvariant, LoopInvariantKind, Mode, SpannedTyped};

use crate::vir_backend::vir_gen::{
    build_span_no_id,
    expr_to_vir::{
        expr::{ast_expr_to_vir_expr, wrap_with_ghost_block},
        types::{ast_type_to_vir_type, make_unit_vir_type},
    },
};

/// The function `assume()` from `fv_std_lib`
static ASSUME: &str = "assume";
/// The function `old()` from `fv_std_lib`
pub static OLD: &str = "old";
/// The function `invariant()` from `fv_std_lib`
pub static INVARIANT: &str = "invariant";
/// The function `decreases()` from `fv_std_lib`
pub static DECREASES: &str = "decreases";

/// Handles function calls from the `fv_std` library and converts them to special VIR expressions.
pub fn handle_fv_std_call(
    call_expr: &Call,
    _mode: Mode, // Reserved for future use with additional `fv_std` functions
    globals: &BTreeMap<GlobalId, (String, Type, Expression)>,
) -> Option<Expr> {
    let ident = match &*call_expr.func {
        Expression::Ident(ident) => ident,
        _ => return None,
    };

    // Convert Noir AST exprs into VIR exprs
    let arguments = call_expr
        .arguments
        .iter()
        .map(|arg| ast_expr_to_vir_expr(arg, Mode::Spec, globals))
        .collect::<Vec<_>>();

    handle_fv_std_inner(&ident.name, arguments, call_expr.location, &call_expr.return_type)
}

/// Handles function calls from the `fv_std` library and converts them to special VIR expressions.
pub fn handle_fv_std_call_in_annotations(
    function_name: &str,
    arguments: &Vec<Expr>,
    location: Location,
    return_typ: &Type,
) -> Option<Expr> {
    handle_fv_std_inner(function_name, arguments.clone(), location, return_typ)
}

fn handle_fv_std_inner(
    function_name: &str,
    arguments: Vec<Expr>,
    location: Location,
    return_typ: &Type,
) -> Option<Expr> {
    match function_name {
        // Special logic for handling the function `assume` from our Noir `fv_std` library
        s if s == ASSUME => {
            assert!(
                arguments.len() == 1,
                "Expected function `assume` from `noir_fv_std` to have exactly one argument"
            );

            let condition_expr = arguments.into_iter().next().unwrap();

            let exprx = ExprX::AssertAssume { is_assume: true, expr: condition_expr };
            let assume_expr = SpannedTyped::new(
                &build_span_no_id("Assume expression".to_string(), Some(location)),
                &make_unit_vir_type(),
                exprx,
            );

            Some(wrap_with_ghost_block(assume_expr, Some(location)))
        }

        // Special logic for handling the function `old` from our Noir `fv_std` library
        s if s == OLD => {
            assert!(
                arguments.len() == 1,
                "Expected function `old` from `noir_fv_std` to have exactly one argument"
            );

            let ExprX::Var(vir_ident) = &arguments[0].x else {
                return None;
            };

            let exprx = ExprX::VarAt(vir_ident.clone(), vir::ast::VarAt::Pre);

            Some(SpannedTyped::new(
                &build_span_no_id(format!("old({})", vir_ident.0), Some(location)),
                &ast_type_to_vir_type(return_typ),
                exprx,
            ))
        }
        s if s == INVARIANT => {
            assert!(
                arguments.len() == 1,
                "Expected function `invariant` from `noir_fv_std` to have exactly one argument"
            );

            let empty_block = SpannedTyped::new(
                &build_span_no_id("Invariant placeholder block".to_string(), Some(location)),
                &make_unit_vir_type(),
                ExprX::Block(Arc::new(Vec::new()), None),
            );

            Some(wrap_with_ghost_block(empty_block, Some(location)))
        }
        s if s == DECREASES => {
            assert!(
                arguments.len() == 1,
                "Expected function `decreases` from `noir_fv_std` to have exactly one argument"
            );

            let empty_block = SpannedTyped::new(
                &build_span_no_id("Decreases placeholder block".to_string(), Some(location)),
                &make_unit_vir_type(),
                ExprX::Block(Arc::new(Vec::new()), None),
            );

            Some(wrap_with_ghost_block(empty_block, Some(location)))
        }

        _ => None,
    }
}

pub fn loop_invariant_from_call(
    call_expr: &Call,
    globals: &BTreeMap<GlobalId, (String, Type, Expression)>,
) -> Option<LoopInvariant> {
    let Expression::Ident(function_ident) = call_expr.func.as_ref() else {
        return None;
    };

    if function_ident.name.as_str() != INVARIANT {
        return None;
    }

    assert!(
        call_expr.arguments.len() == 1,
        "Expected function `invariant` from `noir_fv_std` to have exactly one argument"
    );

    let condition_expr = ast_expr_to_vir_expr(&call_expr.arguments[0], Mode::Spec, globals);

    Some(LoopInvariant { kind: LoopInvariantKind::InvariantAndEnsures, inv: condition_expr })
}

pub fn loop_decreases_from_call(
    call_expr: &Call,
    globals: &BTreeMap<GlobalId, (String, Type, Expression)>,
) -> Option<Expr> {
    let Expression::Ident(function_ident) = call_expr.func.as_ref() else {
        return None;
    };

    if function_ident.name.as_str() != DECREASES {
        return None;
    }

    assert!(
        call_expr.arguments.len() == 1,
        "Expected function `decreases` from `noir_fv_std` to have exactly one argument"
    );

    Some(ast_expr_to_vir_expr(&call_expr.arguments[0], Mode::Spec, globals))
}
