use noirc_frontend::monomorphization::ast::{FuncId, Program};
use vir::ast::Krate;
use vir_gen::Attribute;
use vir_gen::BuildingKrateError;

use crate::param_source::ParamSources;
use crate::vir_backend::{
    lowering::monomorph_ast_optimization_passes, vir_gen::build_krate_with_ready_annotations,
};
pub mod lowering;
pub mod vir_gen;

/// Same as `create_verus_vir` but expects the FV attributes
/// to be already transformed into VIR form.
pub fn create_verus_vir_with_ready_annotations(
    program: Program,
    fv_annotations: Vec<(FuncId, Vec<Attribute>)>,
    param_sources: &ParamSources,
) -> Result<Krate, BuildingKrateError> {
    let program = monomorph_ast_optimization_passes(program, param_sources);
    build_krate_with_ready_annotations(program, fv_annotations, param_sources)
}
