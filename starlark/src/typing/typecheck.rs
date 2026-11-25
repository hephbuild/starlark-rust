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
use starlark_syntax::syntax::ast::AssignP;
use starlark_syntax::syntax::ast::AssignTargetP;
use starlark_syntax::syntax::ast::ClauseP;
use starlark_syntax::syntax::ast::DefP;
use starlark_syntax::syntax::ast::ExprP;
use starlark_syntax::syntax::ast::ForP;
use starlark_syntax::syntax::ast::StmtP;
use starlark_syntax::syntax::ast::Visibility;
use starlark_syntax::syntax::module::AstModuleFields;
use starlark_syntax::syntax::top_level_stmts::top_level_stmts_mut;
use starlark_syntax::syntax::uniplate::Visit;

use crate::codemap::CodeMap;
use crate::codemap::FileSpan;
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
use crate::eval::compiler::scope::payload::CstAssignIdent;
use crate::eval::compiler::scope::payload::CstAssignIdentExt;
use crate::eval::compiler::scope::payload::CstExpr;
use crate::eval::compiler::scope::payload::CstPayload;
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
use crate::values::typing::TypeInstanceId;

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

/// How a name inside a `def` is bound.
#[derive(Debug, Clone, Copy, Dupe, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BindingKind {
    /// A parameter of the def, `*args` and `**kwargs` included.
    Param,
    /// Assigned in the def's body: `x = ...`, `x += ...`, a `for` variable,
    /// or a nested `def`'s name.
    Local,
    /// A comprehension's `for` variable.
    Comprehension,
    /// A lambda's parameter.
    Lambda,
}

impl BindingKind {
    /// The kind as a stable identifier.
    pub fn as_str(self) -> &'static str {
        match self {
            BindingKind::Param => "param",
            BindingKind::Local => "local",
            BindingKind::Comprehension => "comprehension",
            BindingKind::Lambda => "lambda",
        }
    }
}

/// The def path that owns each binding inside a top-level `def`, and how the
/// binding is made. A comprehension's or a lambda's binding is owned by the
/// def it is in. The first way a binding is made wins (a parameter assigned
/// in the body stays a parameter).
struct DefBindingOwners<'c> {
    codemap: &'c CodeMap,
    path: Vec<String>,
    owners: UnorderedMap<BindingId, (Vec<String>, BindingKind)>,
}

impl DefBindingOwners<'_> {
    fn bind(&mut self, ident: &CstAssignIdent, kind: BindingKind) -> Result<(), InternalError> {
        let id = ident.resolved_binding_id(self.codemap)?;
        if self.owners.get(&id).is_none() {
            self.owners.insert(id, (self.path.clone(), kind));
        }
        Ok(())
    }

    fn bind_target(
        &mut self,
        target: &AssignTargetP<CstPayload>,
        kind: BindingKind,
    ) -> Result<(), InternalError> {
        match target {
            AssignTargetP::Identifier(ident) => self.bind(ident, kind),
            AssignTargetP::Tuple(xs) => {
                for x in xs {
                    self.bind_target(x, kind)?;
                }
                Ok(())
            }
            AssignTargetP::Index(_) | AssignTargetP::Dot(..) => Ok(()),
        }
    }

    fn def(&mut self, def: &DefP<CstPayload>) -> Result<(), InternalError> {
        // Defaults and annotations are evaluated in the enclosing scope.
        let mut outer = Vec::new();
        for param in &def.params {
            param.node.visit_expr(|x| outer.push(x));
        }
        for x in outer {
            self.expr(x)?;
        }
        self.path.push(def.name.ident.clone());
        for param in &def.params {
            if let Some(ident) = param.node.ident() {
                self.bind(ident, BindingKind::Param)?;
            }
        }
        self.stmt(&def.body)?;
        self.path.pop();
        Ok(())
    }

    fn stmt(&mut self, stmt: &CstStmt) -> Result<(), InternalError> {
        match &stmt.node {
            StmtP::Def(def) => {
                self.bind(&def.name, BindingKind::Local)?;
                return self.def(def);
            }
            StmtP::Assign(AssignP { lhs, .. }) | StmtP::AssignModify(lhs, ..) => {
                self.bind_target(lhs, BindingKind::Local)?
            }
            StmtP::For(ForP { var, .. }) => self.bind_target(var, BindingKind::Local)?,
            _ => {}
        }
        stmt.visit_children_err(|x| match x {
            Visit::Stmt(x) => self.stmt(x),
            Visit::Expr(x) => self.expr(x),
        })
    }

    fn expr(&mut self, expr: &CstExpr) -> Result<(), InternalError> {
        match &expr.node {
            ExprP::Lambda(lambda) => {
                for param in &lambda.params {
                    if let Some(ident) = param.node.ident() {
                        self.bind(ident, BindingKind::Lambda)?;
                    }
                }
            }
            ExprP::ListComprehension(_, for1, clauses)
            | ExprP::DictComprehension(_, for1, clauses) => {
                self.bind_target(&for1.var, BindingKind::Comprehension)?;
                for clause in clauses {
                    if let ClauseP::For(clause) = clause {
                        self.bind_target(&clause.var, BindingKind::Comprehension)?;
                    }
                }
            }
            _ => {}
        }
        expr.visit_expr_err(|x| self.expr(x))
    }
}

/// A binding inside a top-level `def`.
#[derive(Debug)]
struct DefBinding {
    owner: Vec<String>,
    name: String,
    kind: BindingKind,
    span: Span,
    ty: Ty,
}

/// A module-level name, as [`TypeMap::module_bindings`] reports it.
#[derive(Debug)]
pub struct ModuleBinding<'a> {
    /// The name.
    pub name: &'a str,
    /// The type of its value.
    pub ty: &'a Ty,
    /// The type it denotes in a type annotation, when it is a type (a
    /// record, an enum or an alias such as `Names = list[str]`).
    pub as_type: Option<&'a Ty>,
    /// For a record or enum type this module declares: the type's id (the
    /// one its instances' type carries), and the binding that named it.
    pub declaration: Option<(TypeInstanceId, FileSpan)>,
}

#[derive(Debug)]
struct ModuleBindingData {
    name: String,
    ty: Ty,
    as_type: Option<Ty>,
    declaration: Option<(TypeInstanceId, Span)>,
}

/// Structure containing all the inferred types.
#[derive(Debug)]
pub struct TypeMap {
    codemap: CodeMap,
    bindings: UnorderedMap<BindingId, (String, Span, Ty)>,
    /// Sorted by owner, name and position.
    def_bindings: Vec<DefBinding>,
    /// Sorted by name.
    module_bindings: Vec<ModuleBindingData>,
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
    fn empty(codemap: CodeMap) -> TypeMap {
        TypeMap {
            codemap,
            bindings: UnorderedMap::new(),
            def_bindings: Vec::new(),
            module_bindings: Vec::new(),
        }
    }

    /// Each binding inside a top-level `def`: the def path that owns it
    /// (`["f"]`, or `["f", "g"]` for a def nested in `f`), its name, how it is
    /// bound, and its type. A comprehension's or a lambda's binding is owned
    /// by the def it is in. Sorted by owner, name and position; one name can
    /// be bound more than once under one owner (a local and a comprehension
    /// variable).
    pub fn bindings(&self) -> impl Iterator<Item = (&[String], &str, BindingKind, &Ty)> {
        self.def_bindings
            .iter()
            .map(|b| (b.owner.as_slice(), b.name.as_str(), b.kind, &b.ty))
    }

    /// Each module-level name, private and loaded names included, sorted by
    /// name.
    pub fn module_bindings(&self) -> impl Iterator<Item = ModuleBinding<'_>> {
        self.module_bindings.iter().map(|b| ModuleBinding {
            name: &b.name,
            ty: &b.ty,
            as_type: b.as_type.as_ref(),
            declaration: b.declaration.map(|(id, span)| {
                (
                    id,
                    FileSpan {
                        file: self.codemap.dupe(),
                        span,
                    },
                )
            }),
        })
    }

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
                    TypeMap::empty(codemap),
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
                TypeMap::empty(codemap),
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
                            TypeMap::empty(codemap),
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
                                TypeMap::empty(codemap),
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

        let mut owners = DefBindingOwners {
            codemap: &codemap,
            path: Vec::new(),
            owners: UnorderedMap::new(),
        };
        for top in cst.iter() {
            if let StmtP::Def(def) = &top.node {
                if let Err(e) = owners.def(def) {
                    return (
                        vec![InternalError::into_error(e)],
                        TypeMap::empty(codemap),
                        Interface::default(),
                        Vec::new(),
                    );
                }
            }
        }
        let mut def_bindings: Vec<DefBinding> = owners
            .owners
            .into_hash_map()
            .into_iter()
            .map(|(id, (owner, kind))| {
                let binding = scope_data.get_binding(id);
                let span = match binding.source {
                    BindingSource::Source(span) => span,
                    BindingSource::FromModule => Span::default(),
                };
                // A lambda's parameter is not solved: it is `Any`.
                let ty = match typemap.get(&id) {
                    Some((_, _, ty)) => ty.clone(),
                    None => Ty::any(),
                };
                DefBinding {
                    owner,
                    name: binding.name.as_str().to_owned(),
                    kind,
                    span,
                    ty,
                }
            })
            .collect();
        def_bindings.sort_by(|a, b| {
            (&a.owner, &a.name, a.span.begin(), a.kind).cmp(&(
                &b.owner,
                &b.name,
                b.span.begin(),
                b.kind,
            ))
        });

        let mut module_bindings: Vec<ModuleBindingData> = names
            .all_names_slots_and_visibilities()
            .into_iter()
            .map(|(name, slot, _)| ModuleBindingData {
                name: name.as_str().to_owned(),
                ty: module_var_types
                    .types
                    .get(&slot)
                    .cloned()
                    .unwrap_or_else(Ty::any),
                as_type: module_var_types.as_types.get(&slot).cloned(),
                declaration: module_var_types.declarations.get(&slot).copied(),
            })
            .collect();
        module_bindings.sort_by(|a, b| a.name.cmp(&b.name));

        let typemap = TypeMap {
            bindings: typemap,
            codemap: codemap.dupe(),
            def_bindings,
            module_bindings,
        };

        let errors = [scope_errors, fill_types_errors, all_solve_errors]
            .into_iter()
            .flatten()
            .map(TypingError::into_error)
            .collect();

        let mut declaration_approximations: Vec<_> = module_var_types
            .declaration_approximations
            .entries_unordered()
            .map(|(id, approximation)| (*id, *approximation))
            .collect();
        declaration_approximations.sort_by_key(|(id, _)| *id);
        for (id, approximation) in declaration_approximations {
            approximations.push(Approximation::new(
                "Declaration typed as Any",
                format!(
                    "{}: {}",
                    scope_data.get_binding(id).name.as_str(),
                    approximation.as_str()
                ),
            ));
        }

        let mut res = HashMap::new();
        let mut as_types = HashMap::new();
        for (name, module_slot_id, vis) in names.all_names_slots_and_visibilities() {
            if vis == Visibility::Public {
                let ty = module_var_types
                    .types
                    .get(&module_slot_id)
                    .cloned()
                    .unwrap_or_else(Ty::any);
                res.insert(name.as_str().to_owned(), ty);
                if let Some(as_type) = module_var_types.as_types.get(&module_slot_id) {
                    as_types.insert(name.as_str().to_owned(), as_type.clone());
                }
            }
        }
        let interface = Interface::new_with_types(res, as_types);

        (errors, typemap, interface, approximations)
    }
}
