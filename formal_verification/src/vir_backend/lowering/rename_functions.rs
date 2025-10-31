use std::collections::HashMap;

use noirc_frontend::monomorphization::ast::{
    Assign, Binary, Call, Cast, Definition, Expression, For, Function, Ident, LValue, Let, Literal,
    Match, MatchCase, Program, Unary, While,
};
use noirc_frontend::monomorphization::ast::FuncId;

/// Ensure that every monomorphized function has a unique name. Noir tracks functions by their
/// `FuncId`, but Venir keys definitions by name only. Without this pass, distinct instantiations
/// of generic items (e.g. multiple `eq`) end up sharing the same identifier and Venir rejects the
/// crate with "duplicate specification" errors.
pub fn uniquify_function_names_pass(program: &mut Program) {
    let mut grouped: HashMap<String, Vec<FuncId>> = HashMap::new();
    for function in &program.functions {
        grouped.entry(function.name.clone()).or_default().push(function.id);
    }

    let mut rename_map: HashMap<FuncId, String> = HashMap::new();
    for (name, ids) in grouped {
        if ids.len() <= 1 {
            continue;
        }
        for func_id in ids {
            let new_name = format!("{}__{}", name, func_id.0);
            rename_map.insert(func_id, new_name);
        }
    }

    if rename_map.is_empty() {
        return;
    }

    for function in program.functions.iter_mut() {
        apply_function_renames(function, &rename_map);
    }

    for (_, (_, _, expr)) in program.globals.iter_mut() {
        rename_in_expression(expr, &rename_map);
    }
}

fn apply_function_renames(function: &mut Function, rename_map: &HashMap<FuncId, String>) {
    if let Some(new_name) = rename_map.get(&function.id) {
        function.name = new_name.clone();
    }

    rename_in_expression(&mut function.body, rename_map);
}

fn rename_in_expression(expr: &mut Expression, rename_map: &HashMap<FuncId, String>) {
    match expr {
        Expression::Ident(ident) => rename_ident(ident, rename_map),
        Expression::Literal(literal) => rename_in_literal(literal, rename_map),
        Expression::Block(exprs) => {
            exprs.iter_mut().for_each(|e| rename_in_expression(e, rename_map));
        }
        Expression::Unary(Unary { rhs, .. }) => rename_in_expression(rhs, rename_map),
        Expression::Binary(Binary { lhs, rhs, .. }) => {
            rename_in_expression(lhs, rename_map);
            rename_in_expression(rhs, rename_map);
        }
        Expression::Index(index) => {
            rename_in_expression(&mut index.collection, rename_map);
            rename_in_expression(&mut index.index, rename_map);
        }
        Expression::Cast(Cast { lhs, .. }) => rename_in_expression(lhs, rename_map),
        Expression::For(For { start_range, end_range, block, .. }) => {
            rename_in_expression(start_range, rename_map);
            rename_in_expression(end_range, rename_map);
            rename_in_expression(block, rename_map);
        }
        Expression::Loop(body) => rename_in_expression(body, rename_map),
        Expression::While(While { condition, body }) => {
            rename_in_expression(condition, rename_map);
            rename_in_expression(body, rename_map);
        }
        Expression::If(if_expr) => {
            rename_in_expression(&mut if_expr.condition, rename_map);
            rename_in_expression(&mut if_expr.consequence, rename_map);
            if let Some(alternative) = if_expr.alternative.as_deref_mut() {
                rename_in_expression(alternative, rename_map);
            }
        }
        Expression::Match(Match { cases, default_case, .. }) => {
            cases.iter_mut().for_each(|MatchCase { branch, .. }| {
                rename_in_expression(branch, rename_map);
            });
            if let Some(default_case) = default_case.as_deref_mut() {
                rename_in_expression(default_case, rename_map);
            }
        }
        Expression::Tuple(exprs) => {
            exprs.iter_mut().for_each(|e| rename_in_expression(e, rename_map));
        }
        Expression::ExtractTupleField(expr, _) => rename_in_expression(expr, rename_map),
        Expression::Call(Call { func, arguments, .. }) => {
            rename_in_expression(func, rename_map);
            arguments.iter_mut().for_each(|arg| rename_in_expression(arg, rename_map));
        }
        Expression::Let(Let { expression, .. }) => rename_in_expression(expression, rename_map),
        Expression::Constrain(lhs, _, rhs) => {
            rename_in_expression(lhs, rename_map);
            if let Some(boxed) = rhs.as_deref_mut() {
                rename_in_expression(&mut boxed.0, rename_map);
            }
        }
        Expression::Assign(Assign { lvalue, expression }) => {
            rename_in_lvalue(lvalue, rename_map);
            rename_in_expression(expression, rename_map);
        }
        Expression::Semi(expr) => rename_in_expression(expr, rename_map),
        Expression::Clone(expr) | Expression::Drop(expr) => {
            rename_in_expression(expr, rename_map);
        }
        Expression::Break | Expression::Continue => {}
    }
}

fn rename_in_lvalue(lvalue: &mut LValue, rename_map: &HashMap<FuncId, String>) {
    match lvalue {
        LValue::Ident(ident) => rename_ident(ident, rename_map),
        LValue::Index { array, index, .. } => {
            rename_in_lvalue(array, rename_map);
            rename_in_expression(index, rename_map);
        }
        LValue::MemberAccess { object, .. } => rename_in_lvalue(object, rename_map),
        LValue::Dereference { reference, .. } => rename_in_lvalue(reference, rename_map),
        LValue::Clone(inner) => rename_in_lvalue(inner, rename_map),
    }
}

fn rename_in_literal(literal: &mut Literal, rename_map: &HashMap<FuncId, String>) {
    match literal {
        Literal::Array(array) | Literal::Slice(array) => {
            array.contents.iter_mut().for_each(|c| rename_in_expression(c, rename_map));
        }
        Literal::FmtStr(_, _, expr) => rename_in_expression(expr, rename_map),
        Literal::Integer(_, _, _) | Literal::Bool(_) | Literal::Unit | Literal::Str(_) => {}
    }
}

fn rename_ident(ident: &mut Ident, rename_map: &HashMap<FuncId, String>) {
    if let Definition::Function(func_id) = ident.definition {
        if let Some(new_name) = rename_map.get(&func_id) {
            ident.name = new_name.clone();
        }
    }
}
