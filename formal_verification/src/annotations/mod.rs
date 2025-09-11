use noirc_errors::Location;
use noirc_frontend::monomorphization::ast as mast;
use std::{cell::RefCell, collections::BTreeMap, fmt::Debug, rc::Rc};
use crate::annotations::typing::type_infer::OptionalType;
use ast::{OffsetExpr, SpannedExpr, cata};
use parsing::build_location;

pub mod ast;
pub mod lowering;
pub mod typing;
pub mod parsing;

#[derive(Debug)]
pub struct State<'a> {
    pub function: &'a mast::Function,
    pub global_constants: &'a BTreeMap<mast::GlobalId, (String, mast::Type, mast::Expression)>,
    pub functions: &'a BTreeMap<mast::FuncId, mast::Function>,
    pub min_local_id: Rc<RefCell<u32>>,
}

#[derive(Debug, Clone)]
pub enum Attribute {
    Ghost,
    Ensures(ast::SpannedExpr),
    Requires(ast::SpannedExpr),
}

#[derive(Debug, Clone)]
pub struct MonomorphizationRequest {
    pub function_identifier: String,
    pub param_types: Vec<OptionalType>,
}

fn span_expr(annotation_location: Location, full_length: u32, expr: OffsetExpr) -> SpannedExpr {
    cata(expr, &|(prev_offset, after_offset), exprf| SpannedExpr {
        ann: build_location(annotation_location, full_length, prev_offset, after_offset),
        expr: Box::new(exprf),
    })
}