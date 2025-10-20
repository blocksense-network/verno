use std::{collections::BTreeMap, sync::Arc};

use crate::vir_backend::vir_gen::{
    build_span_no_id,
    expr_to_vir::types::{ast_type_to_vir_type, make_unit_vir_type},
};
use noirc_errors::Location;
use noirc_frontend::monomorphization::ast::{Call, Definition, Expression, GlobalId, Type};
use num_bigint::BigInt;
use num_traits::Zero;
use vir::ast::{Constant, Dt, Expr, ExprX, Mode, SpannedTyped, Stmt};
use vir::ast_util::mk_tuple;

pub type GlobalsMap = BTreeMap<GlobalId, (String, Type, Expression)>;
pub type ExprConverter = fn(&Expression, Mode, &GlobalsMap) -> Expr;
pub type StmtConverter = fn(&Expression, Mode, &GlobalsMap) -> Stmt;

pub fn try_handle_builtin_call(
    call_expr: &Call,
    mode: Mode,
    globals: &GlobalsMap,
    expr_to_vir: ExprConverter,
    expr_to_stmt: StmtConverter,
) -> Option<Expr> {
    let Expression::Ident(function_ident) = call_expr.func.as_ref() else {
        return None;
    };
    let Definition::Builtin(name) = &function_ident.definition else {
        return None;
    };

    match name.as_str() {
        "len" | "array_len" => builtin_len(call_expr),
        "zeroed" => builtin_zeroed(call_expr),
        "checked_transmute" => builtin_checked_transmute(call_expr, mode, globals, expr_to_vir),
        "black_box" => builtin_black_box(call_expr, mode, globals, expr_to_vir),
        "array_refcount" | "slice_refcount" | "slice_push_back" | "slice_push_front"
        | "slice_pop_back" | "slice_pop_front" | "slice_insert" | "slice_remove" => {
            builtin_unit_noop(call_expr, mode, globals, expr_to_stmt, name)
        }
        _ => None,
    }
}

fn builtin_len(call_expr: &Call) -> Option<Expr> {
    if call_expr.arguments.len() != 1 {
        panic!("Expected builtin `len` to receive a single argument");
    }

    let arg_expr = call_expr.arguments.first()?;
    let Some(arg_type) = arg_expr.return_type() else {
        return None;
    };

    let array_length = match arg_type.as_ref() {
        Type::Array(len, _) => *len,
        _ => return None,
    };

    let len_bigint = BigInt::from(array_length as i64);
    let exprx = ExprX::Const(Constant::Int(len_bigint));
    let span = build_span_no_id(
        format!("Builtin len call returning {}", array_length),
        Some(call_expr.location),
    );

    Some(SpannedTyped::new(&span, &ast_type_to_vir_type(&call_expr.return_type), exprx))
}

fn builtin_zeroed(call_expr: &Call) -> Option<Expr> {
    zero_expr_of_type(&call_expr.return_type, Some(call_expr.location))
}

fn builtin_checked_transmute(
    call_expr: &Call,
    mode: Mode,
    globals: &GlobalsMap,
    expr_to_vir: ExprConverter,
) -> Option<Expr> {
    let arg_expr = call_expr.arguments.first()?;
    Some(expr_to_vir(arg_expr, mode, globals))
}

fn builtin_black_box(
    call_expr: &Call,
    mode: Mode,
    globals: &GlobalsMap,
    expr_to_vir: ExprConverter,
) -> Option<Expr> {
    let arg_expr = call_expr.arguments.first()?;
    Some(expr_to_vir(arg_expr, mode, globals))
}

fn builtin_unit_noop(
    call_expr: &Call,
    mode: Mode,
    globals: &GlobalsMap,
    expr_to_stmt: StmtConverter,
    name: &str,
) -> Option<Expr> {
    let mut stmts = Vec::new();
    for arg in &call_expr.arguments {
        stmts.push(expr_to_stmt(arg, mode, globals));
    }
    let span = build_span_no_id(format!("Builtin {} (no-op)", name), Some(call_expr.location));
    let exprx = ExprX::Block(Arc::new(stmts), None);
    Some(SpannedTyped::new(&span, &make_unit_vir_type(), exprx))
}

fn zero_expr_of_type(typ: &Type, location: Option<Location>) -> Option<Expr> {
    match typ {
        Type::Field | Type::Integer(..) => {
            let span = build_span_no_id("Zero literal".to_string(), location);
            Some(SpannedTyped::new(
                &span,
                &ast_type_to_vir_type(typ),
                ExprX::Const(Constant::Int(BigInt::zero())),
            ))
        }
        Type::Bool => {
            let span = build_span_no_id("Bool false literal".to_string(), location);
            Some(SpannedTyped::new(
                &span,
                &ast_type_to_vir_type(typ),
                ExprX::Const(Constant::Bool(false)),
            ))
        }
        Type::Unit => {
            let span = build_span_no_id("Unit literal".to_string(), location);
            Some(SpannedTyped::new(
                &span,
                &ast_type_to_vir_type(typ),
                ExprX::Ctor(
                    Dt::Tuple(0),
                    Arc::new("tuple%0".to_string()),
                    Arc::new(Vec::new()),
                    None,
                ),
            ))
        }
        Type::Array(len, element_type) => {
            let mut elements = Vec::new();
            for _ in 0..*len {
                elements.push(zero_expr_of_type(element_type, location)?);
            }
            let span = build_span_no_id("Array zero literal".to_string(), location);
            Some(SpannedTyped::new(
                &span,
                &ast_type_to_vir_type(typ),
                ExprX::ArrayLiteral(Arc::new(elements)),
            ))
        }
        Type::Tuple(inner_types) => {
            let mut fields = Vec::new();
            for field_type in inner_types {
                fields.push(zero_expr_of_type(field_type, location)?);
            }
            let span = build_span_no_id("Tuple zero literal".to_string(), location);
            Some(mk_tuple(&span, &Arc::new(fields)))
        }
        _ => None,
    }
}
