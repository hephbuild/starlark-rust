/*
 * Copyright 2019 The Starlark in Rust Authors.
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::fmt::Display;

use dupe::Dupe;
use starlark_map::unordered_map::UnorderedMap;
use starlark_syntax::slice_vec_ext::VecExt;
use starlark_syntax::syntax::ast::StmtP;
use starlark_syntax::syntax::ast::Visibility;
use starlark_syntax::syntax::module::AstModuleFields;
use starlark_syntax::syntax::top_level_stmts::top_level_stmts_mut;

use crate::codemap::CodeMap;
use crate::codemap::FileSpanRef;
use crate::codemap::Span;
use crate::codemap::Spanned;
use crate::environment::Globals;
use crate::environment::names::MutableNames;
use crate::environment::slots::ModuleSlotId;
use crate::eval::compiler::scope::BindingId;
use crate::eval::compiler::scope::BindingSource;
use crate::eval::compiler::scope::ModuleScopeData;
use crate::eval::compiler::scope::ModuleScopes;
use crate::eval::compiler::scope::Slot;
use crate::eval::compiler::scope::payload::CstAssignIdentExt;
use crate::eval::compiler::scope::payload::CstStmt;
use crate::eval::compiler::scope::scope_resolver_globals::ScopeResolverGlobals;
use crate::syntax::AstModule;
use crate::syntax::Dialect;
use crate::typing::ParamSpec;
use crate::typing::bindings::Bindings;
use crate::typing::bindings::BindingsCollect;
use crate::typing::bindings::InferReturn;
use crate::typing::ctx::TypingContext;
use crate::typing::error::InternalError;
use crate::typing::error::TypingError;
use crate::typing::fill_types_for_lint::ModuleVarTypes;
use crate::typing::fill_types_for_lint::fill_types_for_lint_typechecker;
use crate::typing::interface::Interface;
use crate::typing::mode::TypecheckMode;
use crate::typing::oracle::ctx::TypingOracleCtx;
use crate::typing::ty::Approximation;
use crate::typing::ty::Ty;
use crate::values::FrozenHeap;

/// What [`solve_bindings`] returns: errors, binding types, approximations, and
/// the inferred type of the collected `def` when it has no return annotation.
pub(crate) type Solved = (
    Vec<TypingError>,
    HashMap<BindingId, Ty>,
    Vec<Approximation>,
    Option<Ty>,
);

// Things which are None in the map have type void - they are never constructed
pub(crate) fn solve_bindings(
    bindings: Bindings,
    oracle: TypingOracleCtx,
    module_var_types: &ModuleVarTypes,
) -> Result<Solved, InternalError> {
    let mut types = bindings
        .expressions
        .keys()
        .map(|x| (*x, Ty::never()))
        .collect::<UnorderedMap<_, _>>();
    for (k, ty) in bindings.types {
        types.insert(k, ty);
    }
    // FIXME: Should be a fixed point, just do 10 iterations since that probably converges
    let mut changed = false;
    let mut ctx = TypingContext {
        oracle,
        errors: RefCell::new(Vec::new()),
        approximoations: RefCell::new(Vec::new()),
        types,
        module_var_types,
    };
    const ITERATIONS: usize = 100;
    for _iteration in 0..ITERATIONS {
        changed = false;
        ctx.errors.borrow_mut().clear();
        for (name, exprs) in &bindings.expressions {
            for expr in exprs {
                let ty = ctx.expression_bind_type(expr)?;
                let t = ctx.types.get_mut(name).unwrap();
                let new = Ty::union2(t.clone(), ty);
                if &new != t {
                    changed = true;
                    *t = new;
                }
            }
        }
        if !changed {
            break;
        }
    }
    if changed {
        ctx.approximoations.borrow_mut().push(Approximation::new(
            "Fixed point didn't converge",
            ITERATIONS,
        ));
    }
    // Make sure we check every expression, looking for failures
    for x in &bindings.check {
        ctx.expression_type(x)?;
    }
    for (span, e, require) in &bindings.check_type {
        let ty = match e {
            None => Ty::none(),
            Some(x) => ctx.expression_type(x)?,
        };
        ctx.validate_type(
            Spanned {
                node: &ty,
                span: *span,
            },
            require,
        )?;
    }
    let inferred = match bindings.infer_return {
        None => None,
        Some(InferReturn {
            params,
            returns,
            falls_through,
        }) => {
            // Every returned expression was checked above: keep only the
            // types, not a second copy of their errors and approximations.
            let errors = ctx.errors.borrow().len();
            let approximations = ctx.approximoations.borrow().len();
            let mut results = Vec::with_capacity(returns.len() + 1);
            for ret in returns {
                results.push(match ret {
                    None => Ty::none(),
                    Some(x) => ctx.expression_type(x)?,
                });
            }
            ctx.errors.borrow_mut().truncate(errors);
            ctx.approximoations.borrow_mut().truncate(approximations);
            if falls_through {
                results.push(Ty::none());
            }
            Some(Ty::function(params, Ty::unions(results)))
        }
    };
    Ok((
        ctx.errors.into_inner(),
        ctx.types.into_hash_map(),
        ctx.approximoations.into_inner(),
        inferred,
    ))
}

/// The module slot a top-level `def` binds, and whether it lacks a return
/// annotation.
fn def_module_slot(
    stmt: &CstStmt,
    scope_data: &ModuleScopeData,
    codemap: &CodeMap,
) -> Result<Option<(ModuleSlotId, bool)>, InternalError> {
    let StmtP::Def(def) = &**stmt else {
        return Ok(None);
    };
    let unannotated = def.return_type.is_none();
    let binding_id = def.name.resolved_binding_id(codemap)?;
    match scope_data.get_binding(binding_id).resolved_slot(codemap)? {
        Slot::Module(slot) => Ok(Some((slot, unannotated))),
        Slot::Local(_) => Err(InternalError::msg(
            "top-level def bound to a local slot",
            def.name.span,
            codemap,
        )),
    }
}

/// Infer the return type of each top-level `def` without a return annotation,
/// and record it in `module_var_types`, so that every other `def` (and the
/// module's interface) sees `def f(x: int): return x + 1` as
/// `def f(x: int) -> int`.
///
/// Each `def` is solved on its own against the module's variable types, so a
/// `def` calling another needs the callee's result first: the `def`s are
/// re-solved until no inferred type changes. They start from `never`, so a
/// recursive `def` takes the type of its non-recursive returns. A name bound
/// anywhere else in the module keeps its declared type, as does every `def`
/// when the types do not settle.
fn infer_top_level_returns(
    cst: &mut [&mut CstStmt],
    oracle: TypingOracleCtx,
    scope_data: &ModuleScopeData,
    codemap: &CodeMap,
    module_var_types: &mut ModuleVarTypes,
    approximations: &mut Vec<Approximation>,
) -> Result<(), InternalError> {
    // The index into `cst`, the slot, and the declared parameters of each
    // `def` whose return type is inferred.
    let mut defs: Vec<(usize, ModuleSlotId, ParamSpec)> = Vec::new();
    // The final pass over each `def` collects and reports approximations;
    // the rounds here would only repeat them.
    let mut ignored_approximations = Vec::new();
    // A name bound by two top-level `def`s keeps its declared type: with
    // identical signatures both match `declared` below, and the first one's
    // returns would win although the second is the one bound at the end.
    let mut def_count: HashMap<ModuleSlotId, usize> = HashMap::new();
    for stmt in cst.iter() {
        if let Some((slot, _)) = def_module_slot(stmt, scope_data, codemap)? {
            *def_count.entry(slot).or_default() += 1;
        }
    }
    for (i, stmt) in cst.iter_mut().enumerate() {
        let Some((slot, true)) = def_module_slot(stmt, scope_data, codemap)? else {
            continue;
        };
        if def_count.get(&slot) != Some(&1) {
            continue;
        }
        let collected = BindingsCollect::collect_one(
            stmt,
            TypecheckMode::Lint,
            codemap,
            &mut ignored_approximations,
        )?;
        let Some(infer) = collected.bindings.infer_return else {
            continue;
        };
        let declared = Ty::function(infer.params.dupe(), Ty::any());
        if module_var_types.types.get(&slot) != Some(&declared) {
            // The name is also bound by an assignment or a `for`.
            continue;
        }
        module_var_types
            .types
            .insert(slot, Ty::function(infer.params.dupe(), Ty::never()));
        defs.push((i, slot, infer.params));
    }
    if defs.is_empty() {
        return Ok(());
    }

    // Each round settles at least one more link of the longest call chain.
    const ITERATIONS: usize = 10;
    for _ in 0..ITERATIONS {
        let mut changed = false;
        for (i, slot, _) in &defs {
            ignored_approximations.clear();
            let collected = BindingsCollect::collect_one(
                cst[*i],
                TypecheckMode::Lint,
                codemap,
                &mut ignored_approximations,
            )?;
            let (.., inferred) = solve_bindings(collected.bindings, oracle, module_var_types)?;
            let Some(ty) = inferred else { continue };
            if module_var_types.types.get(slot) != Some(&ty) {
                module_var_types.types.insert(*slot, ty);
                changed = true;
            }
        }
        if !changed {
            return Ok(());
        }
    }

    for (_, slot, params) in defs {
        module_var_types
            .types
            .insert(slot, Ty::function(params, Ty::any()));
    }
    approximations.push(Approximation::new(
        "Return type inference didn't converge",
        ITERATIONS,
    ));
    Ok(())
}

/// Structure containing all the inferred types.
#[derive(Debug)]
pub struct TypeMap {
    codemap: CodeMap,
    bindings: UnorderedMap<BindingId, (String, Span, Ty)>,
}

impl Display for TypeMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Iteration in unstable order - but that's fine because this is just for diagnostics
        for (_binding_id, (name, span, ty)) in self.bindings.entries_sorted() {
            writeln!(
                f,
                "{} ({}) = {}",
                name,
                FileSpanRef {
                    file: &self.codemap,
                    span: *span
                },
                ty
            )?;
        }
        Ok(())
    }
}

impl TypeMap {
    #[cfg(test)]
    pub(crate) fn find_bindings_by_name<'a>(&'a self, name: &str) -> Vec<&'a Ty> {
        self.bindings
            .entries_sorted()
            .into_iter()
            .filter_map(
                |(_binding_id, (n, _span, ty))| {
                    if name == n { Some(ty) } else { None }
                },
            )
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn find_first_binding<'a>(&'a self) -> Option<&'a Ty> {
        self.bindings
            .entries_unordered()
            .min_by_key(|(id, _)| *id)
            .map(|(_, (_, _, ty))| ty)
    }
}

/// Typecheck a module.
pub trait AstModuleTypecheck {
    /// Typecheck a module.
    fn typecheck(
        self,
        globals: &Globals,
        loads: &HashMap<String, Interface>,
    ) -> (Vec<crate::Error>, TypeMap, Interface, Vec<Approximation>);
}

impl AstModuleTypecheck for AstModule {
    fn typecheck(
        self,
        globals: &Globals,
        loads: &HashMap<String, Interface>,
    ) -> (Vec<crate::Error>, TypeMap, Interface, Vec<Approximation>) {
        let (codemap, statement, _dialect, _) = self.into_parts();
        let names = MutableNames::new();
        let frozen_heap = FrozenHeap::new();
        let (
            scope_errors,
            ModuleScopes {
                mut cst,
                scope_data,
                ..
            },
        ) = ModuleScopes::check_module(
            &names,
            &frozen_heap,
            loads,
            statement,
            ScopeResolverGlobals {
                globals: Some(frozen_heap.alloc_any_value(globals.dupe())),
            },
            frozen_heap.alloc_any_value(codemap.dupe()),
            &Dialect::AllOptionsInternal,
        );
        let scope_errors = scope_errors.into_map(TypingError::from_eval_exception);
        // We don't really need to properly unpack top-level statements,
        // but make it safe against future changes.
        let mut cst: Vec<&mut CstStmt> = top_level_stmts_mut(&mut cst);
        let oracle = TypingOracleCtx { codemap: &codemap };

        let mut approximations = Vec::new();
        let (fill_types_errors, mut module_var_types) = match fill_types_for_lint_typechecker(
            &mut cst,
            oracle,
            &scope_data,
            &mut approximations,
        ) {
            Ok(fill_types_errors) => fill_types_errors,
            Err(e) => {
                return (
                    vec![InternalError::into_error(e)],
                    TypeMap {
                        codemap,
                        bindings: UnorderedMap::new(),
                    },
                    Interface::default(),
                    Vec::new(),
                );
            }
        };

        if let Err(e) = infer_top_level_returns(
            &mut cst,
            oracle,
            &scope_data,
            &codemap,
            &mut module_var_types,
            &mut approximations,
        ) {
            return (
                vec![InternalError::into_error(e)],
                TypeMap {
                    codemap,
                    bindings: UnorderedMap::new(),
                },
                Interface::default(),
                Vec::new(),
            );
        }

        let mut typemap = UnorderedMap::new();
        let mut all_solve_errors = Vec::new();

        for top in cst.iter_mut() {
            if let StmtP::Def(_) = &mut top.node {
                let bindings = match BindingsCollect::collect_one(
                    top,
                    TypecheckMode::Lint,
                    &codemap,
                    &mut approximations,
                ) {
                    Ok(bindings) => bindings,
                    Err(e) => {
                        return (
                            vec![InternalError::into_error(e)],
                            TypeMap {
                                codemap,
                                bindings: UnorderedMap::new(),
                            },
                            Interface::default(),
                            Vec::new(),
                        );
                    }
                };
                let (solve_errors, types, solve_approximations, _) =
                    match solve_bindings(bindings.bindings, oracle, &module_var_types) {
                        Ok(x) => x,
                        Err(e) => {
                            return (
                                vec![e.into_error()],
                                TypeMap {
                                    codemap,
                                    bindings: UnorderedMap::new(),
                                },
                                Interface::default(),
                                Vec::new(),
                            );
                        }
                    };

                all_solve_errors.extend(solve_errors);
                approximations.extend(solve_approximations);

                for (id, ty) in &types {
                    let binding = scope_data.get_binding(*id);
                    let name = binding.name.as_str().to_owned();
                    let span = match binding.source {
                        BindingSource::Source(span) => span,
                        BindingSource::FromModule => Span::default(),
                    };
                    typemap.insert(*id, (name, span, ty.clone()));
                }
            }
        }

        let typemap = TypeMap {
            bindings: typemap,
            codemap: codemap.dupe(),
        };

        let errors = [scope_errors, fill_types_errors, all_solve_errors]
            .into_iter()
            .flatten()
            .map(TypingError::into_error)
            .collect();

        let mut res = HashMap::new();
        for (name, module_slot_id, vis) in names.all_names_slots_and_visibilities() {
            if vis == Visibility::Public {
                let ty = module_var_types
                    .types
                    .get(&module_slot_id)
                    .cloned()
                    .unwrap_or_else(Ty::any);
                res.insert(name.as_str().to_owned(), ty);
            }
        }
        let interface = Interface::new(res);

        (errors, typemap, interface, approximations)
    }
}
