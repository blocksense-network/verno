use noirc_frontend::monomorphization::ast::Program;

use crate::param_source::ParamSources;
use crate::vir_backend::lowering::{
    array_mutation::fix_array_mutation_pass, loop_unroll::unroll_for_loops_pass,
    mut_args::demut_parameters, rename_functions::uniquify_function_names_pass,
    tuple_deconstruction::fix_tuple_deconstruction_pass,
};
pub mod array_mutation;
pub mod loop_unroll;
pub mod mut_args;
pub mod rename_functions;
pub mod tuple_deconstruction;

pub fn monomorph_ast_optimization_passes(
    mut program: Program,
    param_sources: &ParamSources,
) -> Program {
    uniquify_function_names_pass(&mut program);
    fix_tuple_deconstruction_pass(&mut program);
    unroll_for_loops_pass(&mut program);
    fix_array_mutation_pass(&mut program);
    demut_parameters(&mut program, param_sources);
    program
}
