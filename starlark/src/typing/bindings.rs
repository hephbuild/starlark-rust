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

use std::collections::HashMap;

use dupe::Dupe;
use starlark_map::small_map::SmallMap;
use starlark_syntax::syntax::ast::AssignOp;
use starlark_syntax::syntax::ast::AssignP;
use starlark_syntax::syntax::ast::AssignTargetP;
use starlark_syntax::syntax::ast::AstLiteral;
use starlark_syntax::syntax::ast::ClauseP;
use starlark_syntax::syntax::ast::DefP;
use starlark_syntax::syntax::ast::ExprP;
use starlark_syntax::syntax::ast::ForClauseP;
use starlark_syntax::syntax::ast::ForP;
use starlark_syntax::syntax::ast::IdentP;
use starlark_syntax::syntax::ast::StmtP;
use starlark_syntax::syntax::def::DefParamKind;
use starlark_syntax::syntax::def::DefParams;
use starlark_syntax::syntax::def::DefRegularParamMode;
use starlark_syntax::syntax::uniplate::Visit;

use crate::codemap::CodeMap;
use crate::codemap::Span;
use crate::codemap::Spanned;
use crate::eval::compiler::scope::BindingId;
use crate::eval::compiler::scope::ResolvedIdent;
use crate::eval::compiler::scope::payload::CstAssignIdentExt;
use crate::eval::compiler::scope::payload::CstAssignTarget;
use crate::eval::compiler::scope::payload::CstExpr;
use crate::eval::compiler::scope::payload::CstPayload;
use crate::eval::compiler::scope::payload::CstStmt;
use crate::eval::compiler::scope::payload::CstTypeExpr;
use crate::typing::ParamSpec;
use crate::typing::TyBasic;
use crate::typing::arc_ty::ArcTy;
use crate::typing::callable_param::ParamIsRequired;
use crate::typing::error::InternalError;
use crate::typing::mode::TypecheckMode;
use crate::typing::tuple::TyTuple;
use crate::typing::ty::Approximation;
use crate::typing::ty::Ty;
use crate::util::arc_str::ArcStr;

#[derive(Clone)]
pub(crate) enum BindExpr<'a> {
    Expr(&'a CstExpr),
    /// Get this position from the expression
    GetIndex(usize, Box<BindExpr<'a>>),
    Iter(Box<BindExpr<'a>>),
    AssignModify(&'a CstAssignTarget, AssignOp, &'a CstExpr),
    /// Set this index in the variable
    SetIndex(BindingId, &'a CstExpr, Box<BindExpr<'a>>),
    ListAppend(BindingId, &'a CstExpr),
    ListExtend(BindingId, &'a CstExpr),
}

impl<'a> BindExpr<'a> {
    pub(crate) fn span(&self) -> Span {
        match self {
            BindExpr::Expr(x) => x.span,
            BindExpr::GetIndex(_, x) => x.span(),
            BindExpr::Iter(x) => x.span(),
            BindExpr::AssignModify(x, _, _) => x.span,
            BindExpr::SetIndex(_, x, _) => x.span,
            BindExpr::ListAppend(_, x) => x.span,
            BindExpr::ListExtend(_, x) => x.span,
        }
    }
}

#[derive(Default)]
pub(crate) struct Bindings<'a> {
    pub(crate) expressions: SmallMap<BindingId, Vec<BindExpr<'a>>>,
    /// Non-inferred types of bindings: from `load`,
    /// or from variable or function parameter type annotations.
    pub(crate) types: HashMap<BindingId, Ty>,
    /// Expressions which need to be typechecked, but which are not used
    /// in assignments or in other expressions.
    /// For example `expr` in:
    ///
    /// ```python
    /// if expr: ...
    /// ```
    pub(crate) check: Vec<&'a CstExpr>,
    pub(crate) check_type: Vec<(Span, Option<&'a CstExpr>, Ty)>,
    /// Set when the collected statement is a `def` without a return type
    /// annotation: what the solver needs to infer one.
    pub(crate) infer_return: Option<InferReturn<'a>>,
}

/// The parts of an unannotated `def` its return type is inferred from.
pub(crate) struct InferReturn<'a> {
    /// The `def`'s parameters, as in its declared type.
    pub(crate) params: ParamSpec,
    /// Every `return` of this `def`, not of a `def` nested in it.
    /// `None` is a bare `return`.
    pub(crate) returns: Vec<Option<&'a CstExpr>>,
    /// Whether the body can run off its end, which returns `None`.
    pub(crate) falls_through: bool,
}

/// Push every `return` reachable in `stmt` without entering a nested `def`.
fn collect_returns<'a>(stmt: &'a CstStmt, out: &mut Vec<Option<&'a CstExpr>>) {
    match &**stmt {
        StmtP::Return(ret) => out.push(ret.as_ref()),
        StmtP::Statements(stmts) => {
            for stmt in stmts {
                collect_returns(stmt, out);
            }
        }
        StmtP::If(_, body) => collect_returns(body, out),
        StmtP::IfElse(_, branches) => {
            let (then_branch, else_branch) = &**branches;
            collect_returns(then_branch, out);
            collect_returns(else_branch, out);
        }
        StmtP::For(ForP { body, .. }) => collect_returns(body, out),
        // A nested `def` returns from itself; no other statement holds a `return`.
        _ => {}
    }
}

/// Whether running `stmt` can complete normally, i.e. without a `return` or
/// a call to the global `fail`. Errs towards `true`: a `for` loop, or an `if`
/// without `else`, may always fall through.
fn may_fall_through(stmt: &CstStmt) -> bool {
    match &**stmt {
        StmtP::Return(_) => false,
        StmtP::Statements(stmts) => stmts.iter().all(may_fall_through),
        StmtP::IfElse(_, branches) => {
            let (then_branch, else_branch) = &**branches;
            may_fall_through(then_branch) || may_fall_through(else_branch)
        }
        StmtP::Expression(expr) => !is_global_fail_call(expr),
        _ => true,
    }
}

fn is_global_fail_call(expr: &CstExpr) -> bool {
    let ExprP::Call(fun, _) = &**expr else {
        return false;
    };
    match &fun.node {
        ExprP::Identifier(ident) => {
            ident.node.ident == "fail"
                && matches!(ident.node.payload, Some(ResolvedIdent::Global(_)))
        }
        _ => false,
    }
}

/// The type an unannotated parameter takes from its default, when the
/// default is a literal: `1` is `int`, `-1.5` is `int | float`, `"s"` is
/// `str`, `True` is `bool`, and `[...]`, `{...}`, `(...)` are a list, dict or
/// tuple of `Any`. A container's elements are not inferred: `x = []` is
/// filled in later by callers, and `["a"]` is an example, not a schema.
///
/// A float default takes `int | float`, not `float`: `scale = 1.0` reads as
/// "a number", and refusing `f(2)` would be noise. An int default stays
/// `int`.
///
/// `None` infers nothing: `x = None` means "optional something", and typing
/// it `None` would refuse every real argument. Any other expression infers
/// nothing either; the parameter stays `Any`.
///
/// Only the lint typechecker uses this: the body (`visit_def`, in
/// `TypecheckMode::Lint`) and the module-level type callers are checked
/// against (`fill_types_for_lint`) both take parameter types from here. The
/// compiler typechecker keeps `Any`, so evaluation is unchanged.
pub(crate) fn literal_default_ty(expr: &CstExpr) -> Option<Ty> {
    let number = |expr: &CstExpr| match &**expr {
        ExprP::Literal(AstLiteral::Int(_)) => Some(Ty::int()),
        ExprP::Literal(AstLiteral::Float(_)) => Some(Ty::union2(Ty::int(), Ty::float())),
        _ => None,
    };
    match &**expr {
        ExprP::Literal(AstLiteral::String(_)) => Some(Ty::string()),
        ExprP::Literal(_) => number(expr),
        ExprP::Minus(x) | ExprP::Plus(x) => number(x),
        ExprP::Identifier(ident)
            if matches!(ident.node.ident.as_str(), "True" | "False")
                && matches!(ident.node.payload, Some(ResolvedIdent::Global(_))) =>
        {
            Some(Ty::bool())
        }
        ExprP::List(_) => Some(Ty::any_list()),
        ExprP::Dict(_) => Some(Ty::any_dict()),
        ExprP::Tuple(_) => Some(Ty::any_tuple()),
        _ => None,
    }
}

pub(crate) struct BindingsCollect<'a, 'b> {
    pub(crate) bindings: Bindings<'a>,
    pub(crate) approximations: &'b mut Vec<Approximation>,
}

impl<'a, 'b> BindingsCollect<'a, 'b> {
    /// Collect all the assignments to variables.
    ///
    /// This function only fails on internal errors.
    pub(crate) fn collect_one(
        x: &'a mut CstStmt,
        typecheck_mode: TypecheckMode,
        codemap: &CodeMap,
        approximations: &'b mut Vec<Approximation>,
    ) -> Result<Self, InternalError> {
        let mut res = BindingsCollect {
            bindings: Bindings::default(),
            approximations,
        };

        let x: &'a CstStmt = x;
        match &**x {
            StmtP::Def(def) => {
                let params = res.visit_def(def, typecheck_mode, codemap)?;
                if def.return_type.is_none() {
                    let mut returns = Vec::new();
                    collect_returns(&def.body, &mut returns);
                    res.bindings.infer_return = Some(InferReturn {
                        params,
                        returns,
                        falls_through: may_fall_through(&def.body),
                    });
                }
            }
            _ => res.visit(Visit::Stmt(x), &Ty::any(), typecheck_mode, codemap)?,
        }
        Ok(res)
    }

    fn assign(
        &mut self,
        lhs: &'a CstAssignTarget,
        rhs: BindExpr<'a>,
        codemap: &CodeMap,
    ) -> Result<(), InternalError> {
        match &**lhs {
            AssignTargetP::Identifier(x) => {
                self.bindings
                    .expressions
                    .entry(x.resolved_binding_id(codemap)?)
                    .or_default()
                    .push(rhs);
            }
            AssignTargetP::Tuple(xs) => {
                for (i, x) in xs.iter().enumerate() {
                    self.assign(x, BindExpr::GetIndex(i, Box::new(rhs.clone())), codemap)?;
                }
            }
            AssignTargetP::Index(array_index) => match &*array_index.0 {
                ExprP::Identifier(Spanned {
                    span: _,
                    node:
                        IdentP {
                            ident: _name,
                            payload: Some(ResolvedIdent::Slot(_, ident)),
                        },
                }) => {
                    self.bindings
                        .expressions
                        .entry(*ident)
                        .or_default()
                        .push(BindExpr::SetIndex(*ident, &array_index.1, Box::new(rhs)));
                }
                _ => {
                    self.approximations.push(Approximation::new(
                        "Underapproximation",
                        "a.b[x] = .. not handled",
                    ));
                }
            },
            AssignTargetP::Dot(_, _) => {
                self.approximations.push(Approximation::new(
                    "Underapproximation",
                    "a.b = .. not handled",
                ));
            }
        }
        Ok(())
    }

    /// Type must be populated earlier.
    fn resolved_ty(
        expr: &CstTypeExpr,
        typecheck_mode: TypecheckMode,
        codemap: &CodeMap,
    ) -> Result<Ty, InternalError> {
        let ty = match typecheck_mode {
            TypecheckMode::Lint => expr.payload.typechecker_ty.clone(),
            TypecheckMode::Compiler => expr.payload.compiler_ty.clone(),
        };
        match ty {
            Some(ty) => Ok(ty),
            None => Err(InternalError::msg(
                "Type must be populated earlier",
                expr.span,
                codemap,
            )),
        }
    }

    fn resolve_ty_opt(
        expr: Option<&CstTypeExpr>,
        typecheck_mode: TypecheckMode,
        codemap: &CodeMap,
    ) -> Result<Ty, InternalError> {
        match expr {
            Some(expr) => Self::resolved_ty(expr, typecheck_mode, codemap),
            None => Ok(Ty::any()),
        }
    }

    fn visit_def(
        &mut self,
        def: &'a DefP<CstPayload>,
        typecheck_mode: TypecheckMode,
        codemap: &CodeMap,
    ) -> Result<ParamSpec, InternalError> {
        let DefP {
            name,
            params,
            return_type,
            ..
        } = def;
        let DefParams { params, indices: _ } =
            DefParams::unpack(params, codemap).map_err(InternalError::from_eval_exception)?;

        let mut pos_only = Vec::new();
        let mut pos_or_named = Vec::new();
        let mut args = None;
        let mut named_only = Vec::new();
        let mut kwargs = None;

        for p in params {
            let name = &p.node.ident;
            let ty = match (p.node.ty, &p.node.kind, typecheck_mode) {
                (None, DefParamKind::Regular(_, Some(default)), TypecheckMode::Lint) => {
                    literal_default_ty(default).unwrap_or_else(Ty::any)
                }
                (ty, ..) => Self::resolve_ty_opt(ty, typecheck_mode, codemap)?,
            };
            let name_ty = match &p.node.kind {
                DefParamKind::Regular(mode, default_value) => {
                    let required = match default_value.is_some() {
                        true => ParamIsRequired::No,
                        false => ParamIsRequired::Yes,
                    };
                    match mode {
                        DefRegularParamMode::PosOnly => {
                            pos_only.push((required, ty.dupe()));
                        }
                        DefRegularParamMode::PosOrName => {
                            pos_or_named.push((
                                ArcStr::from(name.ident.as_str()),
                                required,
                                ty.dupe(),
                            ));
                        }
                        DefRegularParamMode::NameOnly => {
                            named_only.push((
                                ArcStr::from(name.ident.as_str()),
                                required,
                                ty.dupe(),
                            ));
                        }
                    }
                    Some((name, ty))
                }
                DefParamKind::Args => {
                    // There is the type we require people calling us use (usually any)
                    // and then separately the type we are when we are running (always tuple)
                    args = Some(ty.dupe());
                    Some((name, Ty::basic(TyBasic::Tuple(TyTuple::Of(ArcTy::new(ty))))))
                }
                DefParamKind::Kwargs => {
                    let var_ty = Ty::dict(Ty::string(), ty.clone());
                    kwargs = Some(ty.dupe());
                    Some((name, var_ty))
                }
            };
            if let Some((name, ty)) = name_ty {
                self.bindings
                    .types
                    .insert(name.resolved_binding_id(codemap)?, ty);
            }
        }
        let params2 = ParamSpec::new_parts(pos_only, pos_or_named, args, named_only, kwargs)
            .map_err(|e| InternalError::from_error(e, def.signature_span(), codemap))?;
        let ret_ty = Self::resolve_ty_opt(return_type.as_deref(), typecheck_mode, codemap)?;
        self.bindings.types.insert(
            name.resolved_binding_id(codemap)?,
            Ty::function(params2.dupe(), ret_ty.clone()),
        );
        def.visit_children_err(|x| self.visit(x, &ret_ty, typecheck_mode, codemap))?;
        Ok(params2)
    }

    fn visit(
        &mut self,
        x: Visit<'a, CstPayload>,
        return_type: &Ty,
        typecheck_mode: TypecheckMode,
        codemap: &CodeMap,
    ) -> Result<(), InternalError> {
        match x {
            Visit::Stmt(x) => match &**x {
                StmtP::Assign(AssignP { lhs, ty, rhs }) => {
                    if let Some(ty) = ty {
                        let ty2 = Self::resolved_ty(ty, typecheck_mode, codemap)?;
                        self.bindings
                            .check_type
                            .push((ty.span, Some(rhs), ty2.clone()));
                        if let AssignTargetP::Identifier(id) = &**lhs {
                            // FIXME: This could be duplicated if you declare the type of a variable twice,
                            // we would only see the second one.
                            self.bindings
                                .types
                                .insert(id.resolved_binding_id(codemap)?, ty2);
                        }
                    }
                    self.assign(lhs, BindExpr::Expr(rhs), codemap)?
                }
                StmtP::AssignModify(lhs, op, rhs) => {
                    self.assign(lhs, BindExpr::AssignModify(lhs, *op, rhs), codemap)?
                }
                StmtP::For(ForP { var, over, body: _ }) => {
                    self.assign(var, BindExpr::Iter(Box::new(BindExpr::Expr(over))), codemap)?
                }
                StmtP::Def(def) => {
                    self.visit_def(def, typecheck_mode, codemap)?;
                    // We do our own visit_children, with a different return type
                    return Ok(());
                }
                StmtP::Load(..) => {}
                StmtP::Return(ret) => {
                    self.bindings
                        .check_type
                        .push((x.span, ret.as_ref(), return_type.clone()))
                }
                StmtP::Expression(x) => {
                    // We want to find ident.append(), ident.extend(), ident.extend()
                    // to fake up a BindExpr::ListAppend/ListExtend
                    // so that mutating list operations aren't invisible to us
                    if let ExprP::Call(fun, args) = &**x {
                        if let ExprP::Dot(id, attr) = &***fun {
                            if let ExprP::Identifier(id) = &id.node {
                                let res = match attr.as_str() {
                                    "append" if args.args.len() == 1 => Some((false, 0)),
                                    "insert" if args.args.len() == 2 => Some((false, 1)),
                                    "extend" if args.args.len() == 1 => Some((true, 0)),
                                    _ => None,
                                };
                                if let Some((extend, arg)) = res {
                                    if let ResolvedIdent::Slot(_, id) =
                                        id.node.payload.as_ref().unwrap()
                                    {
                                        let bind = if extend {
                                            BindExpr::ListExtend(*id, args.args[arg].expr())
                                        } else {
                                            BindExpr::ListAppend(*id, args.args[arg].expr())
                                        };
                                        self.bindings.expressions.entry(*id).or_default().push(bind)
                                    }
                                }
                            }
                        }
                    }

                    self.bindings.check.push(x)
                }
                StmtP::If(x, _) => self.bindings.check.push(x),
                StmtP::IfElse(x, _) => self.bindings.check.push(x),
                _ => {}
            },
            Visit::Expr(x) => match &**x {
                ExprP::ListComprehension(_, for1, clauses)
                | ExprP::DictComprehension(_, for1, clauses) => {
                    fn get_for_clause(x: &ClauseP<CstPayload>) -> Option<&ForClauseP<CstPayload>> {
                        match x {
                            ClauseP::For(x) => Some(x),
                            _ => None,
                        }
                    }
                    for x in
                        std::iter::once(&**for1).chain(clauses.iter().filter_map(get_for_clause))
                    {
                        self.assign(
                            &x.var,
                            BindExpr::Iter(Box::new(BindExpr::Expr(&x.over))),
                            codemap,
                        )?
                    }
                }
                _ => {}
            },
        }
        x.visit_children_err(|x| self.visit(x, return_type, typecheck_mode, codemap))?;
        Ok(())
    }
}
