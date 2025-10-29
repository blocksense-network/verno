use crate::annotations::ast::{AnnExpr, SpannedTypedExpr};
use crate::annotations::lowering::convert_structs::convert_struct_access_to_tuple_access;
use crate::annotations::lowering::inline_globals::inline_global_consts;
use crate::annotations::typing::type_conversion::convert_mast_to_noir_type;
use crate::annotations::typing::type_infer::{OptionalType, TypeInferenceError, type_infer};
use crate::annotations::{State, parsing::parse_attribute};
use crate::vir_backend::create_verus_vir_with_ready_annotations;
use crate::vir_backend::vir_gen::expr_to_vir::std_functions::OLD;
use crate::vir_backend::vir_gen::typed_attrs_to_vir::convert_typed_attribute_to_vir_attribute;
use crate::vir_backend::vir_gen::{Attribute, BuildingKrateError};
use fm::FileId;
use iter_extended::vecmap;
use noirc_driver::{CompilationResult, CompileError, CompileOptions, check_crate};
use noirc_errors::Location;
use noirc_errors::{CustomDiagnostic, Span};
use noirc_evaluator::errors::{RuntimeError, SsaReport};
use noirc_frontend::graph::CrateGraph;
use noirc_frontend::hir::def_map::{
    DefMaps, LocalModuleId, ModuleDefId, ModuleId, fully_qualified_module_path,
};
use noirc_frontend::hir_def::expr::HirCallExpression;
use noirc_frontend::hir_def::expr::{HirExpression, HirLiteral};
use noirc_frontend::hir_def::stmt::HirPattern;
use noirc_frontend::monomorphization::ast::LocalId;
use noirc_frontend::node_interner::{ExprId, FunctionModifiers, GlobalValue};
use noirc_frontend::token::SecondaryAttribute;
use noirc_frontend::{Kind, Type as HirType};
use noirc_frontend::{
    debug::DebugInstrumenter,
    graph::CrateId,
    hir::Context,
    monomorphization::{
        Monomorphizer,
        ast::{FuncId, Program},
        debug_types::DebugTypeTracker,
        errors::MonomorphizationError,
        perform_impl_bindings, perform_instantiation_bindings, undo_instantiation_bindings,
    },
    node_interner::{self, NodeInterner},
    parser::ParserError,
    token::SecondaryAttributeKind,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;
use vir::ast::Krate;

use crate::driver::wrapper_errors::{self, CompilationErrorBundle, MonomorphizationErrorBundle};

pub fn compile_and_build_vir_krate(
    context: &mut Context,
    crate_id: CrateId,
    options: &CompileOptions,
) -> CompilationResult<Krate> {
    let (_, warnings) = check_crate(context, crate_id, options)?;

    let main = context.get_main_function(&crate_id).ok_or_else(|| {
        let err = CustomDiagnostic::from_message(
            "cannot compile crate into a program as it does not contain a `main` function",
            FileId::default(),
        );
        vec![err]
    })?;

    modified_compile_for_entry_internal(context, crate_id, main, options, false, warnings)
}

/// The crate that is being provided must have been "checked" and the warnings/errors have been reported
pub fn compile_and_build_vir_for_entry_prechecked(
    context: &mut Context,
    crate_id: CrateId,
    entry_function: node_interner::FuncId,
    options: &CompileOptions,
) -> CompilationResult<Krate> {
    modified_compile_for_entry_internal(
        context,
        crate_id,
        entry_function,
        options,
        false, // Because the warnings have been reported we don't have to "check" the crate again
        Vec::new(),
    )
}

fn modified_compile_for_entry_internal(
    context: &mut Context,
    crate_id: CrateId,
    entry_function: node_interner::FuncId,
    options: &CompileOptions,
    run_check: bool,
    mut warnings: Vec<CustomDiagnostic>,
) -> CompilationResult<Krate> {
    if run_check {
        let (_, new_warnings) = check_crate(context, crate_id, options)?;
        warnings = new_warnings;
    }

    let compiled_program = modified_compile_no_check(context, options, entry_function).map_err(
        |error| match error {
            CompilationErrorBundle::CompileError(compile_error) => vec![compile_error.into()],
            CompilationErrorBundle::FvError(fv_monomorphization_error) => {
                vec![fv_monomorphization_error.into()]
            }
            CompilationErrorBundle::TypeError(type_check_error) => {
                vec![CustomDiagnostic::from(&type_check_error)]
            }
            CompilationErrorBundle::ParserErrors(parser_errors) => {
                parser_errors.into_iter().map(CustomDiagnostic::from).collect()
            }
            CompilationErrorBundle::ResolverError(resolver_error) => {
                vec![CustomDiagnostic::from(&resolver_error)]
            }
        },
    )?;

    let compilation_warnings = vecmap(compiled_program.warnings.clone(), CustomDiagnostic::from);
    if options.deny_warnings && !compilation_warnings.is_empty() {
        return Err(compilation_warnings);
    }
    if !options.silence_warnings {
        warnings.extend(compilation_warnings);
    }

    Ok((compiled_program.krate, warnings))
}

// Something like the method `compile_no_check()`
fn modified_compile_no_check(
    context: &mut Context,
    options: &CompileOptions,
    main_function: node_interner::FuncId,
) -> Result<KrateAndWarnings, CompilationErrorBundle> {
    let force_unconstrained = options.force_brillig || options.minimal_ssa;

    let (program, fv_annotations) = modified_monomorphize(
        main_function,
        &mut context.def_interner,
        &DebugInstrumenter::default(),
        force_unconstrained,
        &context.crate_graph,
        &context.def_maps,
    )
    .map_err(|e| match e {
        MonomorphizationErrorBundle::MonomorphizationError(monomorphization_error) => {
            CompilationErrorBundle::CompileError(CompileError::MonomorphizationError(
                monomorphization_error,
            ))
        }
        MonomorphizationErrorBundle::FvError(fv_monomorphization_error) => {
            CompilationErrorBundle::FvError(fv_monomorphization_error)
        }
        MonomorphizationErrorBundle::TypeError(type_check_error) => {
            CompilationErrorBundle::TypeError(type_check_error)
        }
        MonomorphizationErrorBundle::ParserErrors(parser_errors) => {
            CompilationErrorBundle::ParserErrors(parser_errors)
        }
        MonomorphizationErrorBundle::ResolverError(resolver_error) => {
            CompilationErrorBundle::ResolverError(resolver_error)
        }
    })?;

    if options.show_monomorphized {
        println!("{program}");
    }

    Ok(KrateAndWarnings {
        krate: create_verus_vir_with_ready_annotations(program, fv_annotations)
            .map_err(|BuildingKrateError::Error(msg)| {
                RuntimeError::InternalError(noirc_evaluator::errors::InternalError::General {
                    message: msg,
                    call_stack: vec![],
                })
            })
            .map_err(|runtime_error| {
                CompilationErrorBundle::CompileError(CompileError::RuntimeError(runtime_error))
            })?,
        warnings: vec![],
        parse_annotations_errors: vec![], // TODO(totel): Get the errors from `modified_monomorphize()`
    })
}

pub enum TypedAttribute {
    Ghost,
    Requires(SpannedTypedExpr),
    Ensures(SpannedTypedExpr),
}

fn modified_monomorphize(
    main: node_interner::FuncId,
    interner: &mut NodeInterner,
    debug_instrumenter: &DebugInstrumenter,
    force_unconstrained: bool,
    crate_graph: &CrateGraph,
    def_maps: &DefMaps,
) -> Result<(Program, Vec<(FuncId, Vec<Attribute>)>), MonomorphizationErrorBundle> {
    let debug_type_tracker = DebugTypeTracker::build_from_debug_instrumenter(debug_instrumenter);
    let mut monomorphizer = Monomorphizer::new(interner, debug_type_tracker, force_unconstrained);
    let function_sig = monomorphizer
        .compile_main(main)
        .map_err(MonomorphizationErrorBundle::MonomorphizationError)?;
    let mut new_ids_to_old_ids: HashMap<FuncId, node_interner::FuncId> = HashMap::new();
    new_ids_to_old_ids.insert(Program::main_id(), main);

    if let Some((old_id, new_id, ..)) = monomorphizer.peek_queue() {
        // Update the map of the new func ids to old ids
        new_ids_to_old_ids.insert(*new_id, *old_id);
    }

    while monomorphizer
        .process_next_job()
        .map_err(|e| MonomorphizationErrorBundle::MonomorphizationError(e))?
    {
        if let Some((old_id, new_id, ..)) = monomorphizer.peek_queue() {
            // Update the map of the new func ids to old ids
            new_ids_to_old_ids.insert(*new_id, *old_id);
        }
    }

    // Clone because of the borrow checker
    let globals = monomorphizer.finished_globals().clone().into_iter().collect::<BTreeMap<_, _>>();

    let min_available_id: u32 =
        monomorphizer.locals().values().map(|LocalId(id)| *id).max().unwrap_or_default() + 1;
    let min_available_id = Rc::new(RefCell::new(min_available_id));

    let functions_to_process: Vec<(FuncId, node_interner::FuncId)> = monomorphizer
        .finished_functions()
        .keys()
        .rev()
        .copied()
        .filter_map(|new_func_id| {
            new_ids_to_old_ids.get(&new_func_id).map(|old_id| (new_func_id, *old_id))
        })
        .collect();

    let mut fv_annotations = Vec::with_capacity(functions_to_process.len());
    // Functions which get resolved via a MonomorphRequest we have to
    // manually add ghost attributes to them.
    let mut to_be_added_ghost_attribute: HashSet<FuncId> = HashSet::new();

    // Initialize the globals map and a tracker for the last seen crate ID outside the loop.
    let mut globals_with_paths: HashMap<String, GlobalValue> = HashMap::new();
    let mut last_crate_id: Option<CrateId> = None;

    for (new_func_id, old_id) in functions_to_process {
        let parameters_hir_types: HashMap<String, noirc_frontend::Type> =
            collect_parameter_hir_types(&monomorphizer, &old_id);

        // Determine the crate ID of the function currently being processed.
        let current_func_crate_id = monomorphizer.interner().function_meta(&old_id).source_crate;
        let current_func_module_id = monomorphizer.interner().function_meta(&old_id).source_module;

        // Conditionally update the globals map based on the current crate context.
        update_globals_if_needed(
            &mut last_crate_id,
            &mut globals_with_paths,
            current_func_crate_id,
            current_func_module_id,
            &monomorphizer,
            def_maps,
            crate_graph,
        );

        let attribute_data: Vec<_> = monomorphizer
            .interner()
            .function_attributes(&old_id)
            .secondary
            .iter()
            .filter_map(|attribute| {
                if let SecondaryAttributeKind::Tag(annotation) = &attribute.kind {
                    Some((annotation.as_str().to_owned(), attribute.location))
                } else {
                    None
                }
            })
            .collect();

        let mut processed_attributes = Vec::new();

        for (annotation_body, location) in attribute_data {
            let function_for_parser = &monomorphizer.finished_functions()[&new_func_id];

            // NOTE: #['...]
            //       ^^^^^^^ - received `Location`
            //          ^^^  - relevant stuff
            let location = Location {
                span: Span::inclusive(location.span.start() + 3, location.span.end() - 1),
                ..location
            };

            let parsed_attribute = parse_attribute(
                &annotation_body,
                location,
                function_for_parser,
                &globals,
                &monomorphizer.finished_functions(),
            )
            .map_err(|e| MonomorphizationErrorBundle::ParserErrors(e.0))?;
            // Ghost functions always get a monomorphization request because
            // they are not part of the monomorphizer.finished_functions
            let typed_attribute = match parsed_attribute {
                crate::annotations::Attribute::Ghost => TypedAttribute::Ghost,
                crate::annotations::Attribute::Ensures(expr) => {
                    let typed_expr = type_infer_attribute_expr(
                        &mut monomorphizer,
                        new_func_id,
                        &globals,
                        min_available_id.clone(),
                        &parameters_hir_types,
                        &globals_with_paths,
                        expr,
                        &mut new_ids_to_old_ids,
                        &mut to_be_added_ghost_attribute,
                    )?;
                    TypedAttribute::Ensures(typed_expr)
                }
                crate::annotations::Attribute::Requires(expr) => {
                    let typed_expr = type_infer_attribute_expr(
                        &mut monomorphizer,
                        new_func_id,
                        &globals,
                        min_available_id.clone(),
                        &parameters_hir_types,
                        &globals_with_paths,
                        expr,
                        &mut new_ids_to_old_ids,
                        &mut to_be_added_ghost_attribute,
                    )?;
                    TypedAttribute::Requires(typed_expr)
                }
            };

            let final_state = State {
                function: &monomorphizer.finished_functions()[&new_func_id],
                global_constants: &globals,
                functions: &monomorphizer.finished_functions(),
                min_local_id: min_available_id.clone(),
            };

            processed_attributes
                .push(convert_typed_attribute_to_vir_attribute(typed_attribute, &final_state));
        }

        fv_annotations.push((new_func_id, processed_attributes));
    }

    to_be_added_ghost_attribute.into_iter().for_each(|func_id| {
        fv_annotations.push((func_id, vec![Attribute::Ghost]));
    });

    let program = monomorphizer.into_program(function_sig);

    Ok((program.handle_ownership(), fv_annotations))
}

pub struct KrateAndWarnings {
    pub krate: Krate,
    pub warnings: Vec<SsaReport>,
    pub parse_annotations_errors: Vec<ParserError>,
}

// Helper function using a bounded for-loop for safer retries.
/// Does type inferring and processes monomorphization requests.
/// Returns the typed attribute expression and a flag if monomorphization
/// request was processed.
fn type_infer_attribute_expr(
    monomorphizer: &mut Monomorphizer,
    new_func_id: FuncId,
    globals: &BTreeMap<
        noirc_frontend::monomorphization::ast::GlobalId,
        (
            String,
            noirc_frontend::monomorphization::ast::Type,
            noirc_frontend::monomorphization::ast::Expression,
        ),
    >,
    min_available_id: Rc<RefCell<u32>>,
    parameters_hir_types: &HashMap<String, noirc_frontend::Type>,
    pathed_globals_with_values: &HashMap<String, GlobalValue>,
    expr: AnnExpr<Location>,
    new_ids_to_old_ids: &mut HashMap<FuncId, node_interner::FuncId>,
    to_be_added_ghost_attribute: &mut HashSet<FuncId>,
) -> Result<SpannedTypedExpr, MonomorphizationErrorBundle> {
    // Set a reasonable limit to prevent infinite loops in case of a bug.
    const MAX_RETRIES: u32 = 100;
    // TODO(totel): Check if a monomorphization request was send for the same function twice
    // This will indicate that we have reached an infinite recursion point. (Some would call it a fix point)
    for _ in 0..MAX_RETRIES {
        // The following two variables are defined inside of the `for` loop
        // because of the borrow checker.
        let function = &monomorphizer.finished_functions()[&new_func_id];
        let state = State {
            function,
            global_constants: &globals,
            functions: &monomorphizer.finished_functions(),
            min_local_id: min_available_id.clone(),
        };

        let expr = convert_struct_access_to_tuple_access(expr.clone(), parameters_hir_types)
            .map_err(|e| {
                match e {
                crate::annotations::lowering::convert_structs::ResolverOrTypeError::ResolverError(
                    resolver_error,
                ) => MonomorphizationErrorBundle::ResolverError(resolver_error),
                crate::annotations::lowering::convert_structs::ResolverOrTypeError::TypeError(
                    type_check_error,
                ) => MonomorphizationErrorBundle::TypeError(type_check_error),
            }
            })?;

        let param_names: Vec<&str> = state
            .function
            .parameters
            .iter()
            .map(|(_, _, param_name, _, _)| param_name.as_str())
            .collect();
        // NOTE: If a global variable is added to the scope via `use foo::x` it wont be added to
        // the `finished_globals` map unless it's being used somewhere in a function's body.
        // Therefore the user has to use the full path for global variables even though they
        // are added to the scope.

        // NOTE: Because the `finished_globals` map doesn't contain
        // all globals but only the ones which are used inside of function's
        // body and the fact that we can not easily add values to that map,
        // we are doing the following:
        // We are gathering all globals from the HIR form of the AST.
        // We visit the FV annotation AST and if we encounter a node which
        // is a global variable, we inline the const value of that global variable.

        let expr = inline_global_consts(expr, pathed_globals_with_values, &param_names)
            .map_err(MonomorphizationErrorBundle::ResolverError)?;

        match type_infer(&state, expr.clone()) {
            Ok(typed_expr) => {
                // Success, return immediately.
                return Ok(typed_expr);
            }
            Err(type_error) => match type_error {
                TypeInferenceError::MonomorphizationRequest(request) => {
                    // This is a recoverable error. Try to resolve it.
                    monomorphize_one_function(
                        &request.function_identifier,
                        request.param_types,
                        monomorphizer,
                        new_ids_to_old_ids,
                        to_be_added_ghost_attribute,
                    )?;
                    // After monomorphizing the function try to type infer again.
                }
                other_error => {
                    // This is an unrecoverable error, return immediately.
                    return Err(MonomorphizationErrorBundle::from(other_error));
                }
            },
        }
    }

    // If the loop finishes, we've exceeded the retry limit. This indicates a likely bug.
    // TODO(totel): Define a better error
    panic!("Monomorphization limit reached")
}

fn monomorphize_one_function(
    func_name: &str,
    param_types: Vec<OptionalType>,
    monomorphizer: &mut Monomorphizer,
    new_ids_to_old_ids: &mut HashMap<FuncId, node_interner::FuncId>,
    to_be_added_ghost_attribute: &mut HashSet<FuncId>,
) -> Result<(), MonomorphizationErrorBundle> {
    // TODO(totel): Change expect!() to something else
    let hir_func_id = monomorphizer
        .interner()
        .find_function(func_name)
        .expect(&format!("Function {} was not found in the node interner", func_name));

    let hir_param_types: Vec<_> = param_types
        .into_iter()
        .map(|typ| {
            convert_mast_to_noir_type(
                typ.unwrap_or(noirc_frontend::monomorphization::ast::Type::Field),
            )
        })
        .collect();

    let new_fn_id = monomorphize_function_by_func_id(monomorphizer, hir_func_id, &hir_param_types)
        .map_err(|e| MonomorphizationErrorBundle::MonomorphizationError(e))?;
    new_ids_to_old_ids.insert(new_fn_id, hir_func_id);
    if has_ghost_attribute(monomorphizer.interner().function_modifiers(&hir_func_id)) {
        to_be_added_ghost_attribute.insert(new_fn_id);
    } else if func_name == OLD {
        // Note: We don't want to monomorphize `fv_std::old` into
        // a ghost function because we may get a verifier error for
        // having a ghost function with a mut reference parameter type.

        // The function call to `fv_std::old` gets converted to a special
        // Verus expressions anyways. Therefore the function `old` is not
        // being actually called anywhere in the code.

        // Therefore we don't want to produce an error
    } else {
        // A non-ghost function has been called in a FV annotation.
        // This isn't allowed and we have to produce an adequate error.

        return Err(MonomorphizationErrorBundle::FvError(
            wrapper_errors::FvMonomorphizationError::ExecInSpecError {
                func_name: func_name.to_string(),
                location: monomorphizer.interner().function_meta(&hir_func_id).location,
            },
        ));
    }

    Ok(())
}

pub fn monomorphize_function_by_func_id(
    monomorphizer: &mut Monomorphizer,
    func_id: node_interner::FuncId,
    param_types: &[HirType],
) -> Result<FuncId, MonomorphizationError> {
    let function_meta = monomorphizer.interner().function_meta(&func_id).clone();
    let param_count = function_meta.parameters.len();

    assert_eq!(
        param_types.len(),
        param_count,
        "monomorphize_function_by_name called with the wrong number of parameter types",
    );

    let func_expr_id = monomorphizer.interner().function(&func_id).as_expr();

    let (_, mut type_bindings) = HirType::Unit.instantiate(&monomorphizer.interner());

    for (index, (_pattern, param_type, _)) in function_meta.parameters.0.iter().enumerate() {
        let binding_type = param_types[index].clone();

        match param_type.follow_bindings() {
            HirType::NamedGeneric(named_generic) => {
                type_bindings.insert(
                    named_generic.type_var.id(),
                    (named_generic.type_var.clone(), Kind::Normal, binding_type),
                );
            }
            HirType::TypeVariable(type_var) => {
                type_bindings.insert(type_var.id(), (type_var.clone(), Kind::Normal, binding_type));
            }
            _ => {}
        }
    }

    let function_type = monomorphizer.interner().id_type(func_expr_id);
    let queued_id = {
        let turbofish_generics = Vec::new();

        let location = Location::dummy();
        let bindings = &type_bindings;
        let bindings = monomorphizer.follow_bindings(bindings);
        monomorphizer.queue_function_with_bindings(
            func_id,
            location,
            bindings,
            function_type.clone(),
            turbofish_generics,
            None,
        )
    };

    monomorphizer.process_queue()?;

    Ok(queued_id)
}

fn has_ghost_attribute(func_modifiers: &FunctionModifiers) -> bool {
    func_modifiers.attributes.secondary.iter().any(|SecondaryAttribute { kind, location: _ }| {
        matches!(kind, SecondaryAttributeKind::Tag(tag) if tag == "ghost")
    })
}

fn collect_parameter_hir_types(
    monomorphizer: &Monomorphizer,
    old_id: &node_interner::FuncId,
) -> HashMap<String, noirc_frontend::Type> {
    let interner = &monomorphizer.interner();
    let func_meta = interner.function_meta(old_id);

    let mut struct_arguments: HashMap<String, noirc_frontend::Type> = func_meta
        .parameters
        .0
        .iter()
        .map(|(hir_pattern, typ, _)| {
            // Extract identifier from the pattern
            let ident = match hir_pattern {
                HirPattern::Identifier(ident) => ident,
                HirPattern::Mutable(inner, _) => match inner.as_ref() {
                    HirPattern::Identifier(ident) => ident,
                    // NOTE: We assume that only the Hir patterns "Identifier" and "Mutable"
                    // appear for function parameters
                    other => unreachable!(
                        "Expected HirPattern::Identifier inside HirPattern::Mutable, got: {:?}",
                        other
                    ),
                },
                other => unreachable!(
                    "Expected HirPattern::Identifier or HirPattern::Mutable, got: {:?}",
                    other
                ),
            };

            (interner.definition(ident.id).name.clone(), typ.clone())
        })
        .collect();

    struct_arguments.insert("result".to_string(), func_meta.return_type().clone());

    struct_arguments
}

/// Updates the `globals_with_paths` map if the current function belongs to a new crate.
///
/// The fully qualified paths of globals are relative to the crate being processed.
/// This function checks if the `current_func_crate_id` is different from the last one seen.
/// If it is, it re-calculates the paths for all globals and updates the map.
/// Otherwise, the existing map is considered valid and is not modified.
fn update_globals_if_needed(
    last_crate_id: &mut Option<CrateId>,
    globals_with_paths: &mut HashMap<String, GlobalValue>,
    current_func_crate_id: CrateId,
    current_func_module_id: LocalModuleId,
    monomorphizer: &Monomorphizer,
    def_maps: &DefMaps,
    crate_graph: &CrateGraph,
) {
    if last_crate_id.map_or(true, |id| id != current_func_crate_id) {
        let fully_imported_globals: HashMap<_, _> = def_maps[&current_func_crate_id]
            [current_func_module_id]
            .scope()
            .values()
            .into_iter()
            .filter_map(|(identifier, map)| match map.get(&None) {
                Some((ModuleDefId::GlobalId(id), ..)) => Some((id, identifier)),
                _ => None,
            })
            .collect();

        *globals_with_paths = monomorphizer
            .interner()
            .get_all_globals()
            .iter()
            .filter(|global_info| {
                // NOTE(totel): If we are verifying a file with an entry point other than `main` we have to make
                // sure that we can build the fully qualified path name for the globals.
                // I believe because the current crate may not be root some mismatch happens when
                // pulling all globals from the interner. Therefore we skip the globals that are
                // not accessable from our current crate.
                let module_id =
                    ModuleId { krate: global_info.crate_id, local_id: global_info.local_id };
                module_id.krate == current_func_crate_id
                    || find_dependencies_helper(
                        crate_graph,
                        &current_func_crate_id,
                        &module_id.krate,
                    )
                    .is_some()
            })
            .map(|global_info| {
                let module_id =
                    ModuleId { krate: global_info.crate_id, local_id: global_info.local_id };

                let mut module_path = fully_qualified_module_path(
                    def_maps,
                    crate_graph,
                    &current_func_crate_id,
                    module_id,
                );
                // HACK: The function `fully_qualified_module_path` fails to consistently add `::`
                // at the end of each path. Therefore we manually add double colons if they are missing.
                if !module_path.ends_with("::") {
                    module_path.push_str("::");
                }

                let full_path =
                    if let Some(identifier) = fully_imported_globals.get(&global_info.id) {
                        identifier.identifier().to_string()
                    } else {
                        format!("{}{}", module_path, global_info.ident.as_str())
                    };

                (full_path, global_info.value.clone())
            })
            .collect();

        *last_crate_id = Some(current_func_crate_id);
    }
}

// Function which was copied from Noir. For some reason this function is `pub(crate)`
// instead of `pub` even though you can remake it from using the public api of the CrateGraph.
fn find_dependencies_helper(
    crate_graph: &CrateGraph,
    crate_id: &CrateId,
    target_crate_id: &CrateId,
) -> Option<Vec<String>> {
    crate_graph[crate_id]
        .dependencies
        .iter()
        .find_map(|dep| {
            if &dep.crate_id == target_crate_id { Some(vec![dep.name.to_string()]) } else { None }
        })
        .or_else(|| {
            crate_graph[crate_id].dependencies.iter().find_map(|dep| {
                if let Some(mut path) =
                    find_dependencies_helper(crate_graph, &dep.crate_id, target_crate_id)
                {
                    path.insert(0, dep.name.to_string());
                    Some(path)
                } else {
                    None
                }
            })
        })
}
