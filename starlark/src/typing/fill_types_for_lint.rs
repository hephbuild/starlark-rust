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

use std::fmt::Display;
use std::iter;

use dupe::Dupe;
use starlark_map::small_map::SmallMap;
use starlark_map::unordered_map;
use starlark_map::unordered_map::UnorderedMap;
use starlark_syntax::slice_vec_ext::SliceExt;
use starlark_syntax::syntax::ast::ArgumentP;
use starlark_syntax::syntax::ast::AssignP;
use starlark_syntax::syntax::ast::AssignTargetP;
use starlark_syntax::syntax::ast::AstLiteral;
use starlark_syntax::syntax::ast::AstString;
use starlark_syntax::syntax::ast::BinOp;
use starlark_syntax::syntax::ast::CallArgsP;
use starlark_syntax::syntax::ast::DefP;
use starlark_syntax::syntax::ast::ExprP;
use starlark_syntax::syntax::ast::ForP;
use starlark_syntax::syntax::ast::LoadArgP;
use starlark_syntax::syntax::ast::LoadP;
use starlark_syntax::syntax::ast::StmtP;
use starlark_syntax::syntax::def::DefParamKind;
use starlark_syntax::syntax::def::DefParams;
use starlark_syntax::syntax::def::DefRegularParamMode;
use starlark_syntax::syntax::type_expr::TypeExprUnpackP;
use starlark_syntax::syntax::type_expr::TypePathP;

use crate::codemap::Span;
use crate::codemap::Spanned;
use crate::environment::slots::ModuleSlotId;
use crate::eval::compiler::constants::Constants;
use crate::eval::compiler::scope::BindingId;
use crate::eval::compiler::scope::ModuleScopeData;
use crate::eval::compiler::scope::ResolvedIdent;
use crate::eval::compiler::scope::Slot;
use crate::eval::compiler::scope::payload::CstAssignIdent;
use crate::eval::compiler::scope::payload::CstAssignIdentExt;
use crate::eval::compiler::scope::payload::CstExpr;
use crate::eval::compiler::scope::payload::CstIdent;
use crate::eval::compiler::scope::payload::CstPayload;
use crate::eval::compiler::scope::payload::CstStmt;
use crate::eval::compiler::scope::payload::CstTypeExpr;
use crate::typing::Approximation;
use crate::typing::ParamSpec;
use crate::typing::Ty;
use crate::typing::TypingOracleCtx;
use crate::typing::bindings::literal_default_ty;
use crate::typing::call_args::TyCallArgs;
use crate::typing::callable_param::ParamIsRequired;
use crate::typing::error::InternalError;
use crate::typing::error::TypingError;
use crate::typing::error::TypingOrInternalError;
use crate::util::arc_str::ArcStr;
use crate::values::Heap;
use crate::values::Value;
use crate::values::ValueLike;
use crate::values::enumeration::EnumType;
use crate::values::function::BoundMethod;
use crate::values::function::NativeFunction;
use crate::values::function::SpecialBuiltinFunction;
use crate::values::record::field::Field;
use crate::values::record::field::FieldGen;
use crate::values::record::record_type::RecordType;
use crate::values::tuple::AllocTuple;
use crate::values::types::ellipsis::Ellipsis;
use crate::values::typing::type_compiled::compiled::TypeCompiled;

/// Why the pre-pass types a `record(...)` or `enum(...)` declaration as
/// `Any` instead of the type evaluation gives it.
#[derive(Debug, Clone, Copy, Dupe, PartialEq, Eq, Hash)]
pub(crate) enum DeclarationApproximation {
    /// Declared under `if` or `for` at the top level.
    ConditionalBinding,
    /// The name is bound more than once at the top level.
    Rebound,
    /// An `enum(...)` variant is not a string literal.
    NonLiteralVariant,
    /// The call has `*args` or `**kwargs`.
    StarArgs,
    /// Declared inside a `def`.
    InDef,
    /// The call is one evaluation rejects (positional arguments to `record`,
    /// a duplicate variant, no fields or no variants).
    InvalidDeclaration,
}

impl DeclarationApproximation {
    /// The reason as a stable identifier.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            DeclarationApproximation::ConditionalBinding => "conditional_binding",
            DeclarationApproximation::Rebound => "rebound",
            DeclarationApproximation::NonLiteralVariant => "non_literal_variant",
            DeclarationApproximation::StarArgs => "star_args",
            DeclarationApproximation::InDef => "in_def",
            DeclarationApproximation::InvalidDeclaration => "invalid_declaration",
        }
    }
}

/// Value computed during partial evaluation of globals.
#[derive(Clone)]
struct GlobalValue<'v> {
    /// `None` means we don't know (or know it may have different value depending on condition).
    value: Option<Value<'v>>,
    ty: Ty,
    /// The type this name denotes in a type annotation, when it has no
    /// `value`. Set only for a loaded name that is a type in the module that
    /// declares it (a record, an enum or an alias), from its interface.
    as_type: Option<Ty>,
    /// Set when this is a record or enum declaration typed as `Any`.
    approximation: Option<DeclarationApproximation>,
}

impl<'v> GlobalValue<'v> {
    fn union2(a: GlobalValue<'v>, b: GlobalValue<'v>) -> GlobalValue<'v> {
        // A variable was potentially assigned more than once, e.g.
        // ```
        // if cond:
        //   x = "A"
        // else:
        //   x = "B"
        // ```
        // So here we say that we don't know what is the value.
        // We could check if both values are equal, use that equal value,
        // but values referenced by the types should not be defined conditionally.
        let approximation = if a.is_declaration() || b.is_declaration() {
            Some(DeclarationApproximation::Rebound)
        } else {
            None
        };
        GlobalValue {
            value: None,
            ty: Ty::union2(a.ty, b.ty),
            as_type: None,
            approximation,
        }
    }

    /// A record or enum type, or a declaration of one typed as `Any`.
    fn is_declaration(&self) -> bool {
        self.approximation.is_some()
            || self.value.is_some_and(|v| {
                v.downcast_ref::<RecordType>().is_some() || v.downcast_ref::<EnumType>().is_some()
            })
    }
}

impl<'v> GlobalValue<'v> {
    fn value(value: Value<'v>) -> GlobalValue<'v> {
        GlobalValue {
            value: Some(value),
            ty: Ty::of_value(value),
            as_type: None,
            approximation: None,
        }
    }

    fn any() -> GlobalValue<'v> {
        GlobalValue::ty(Ty::any())
    }

    fn ty(ty: Ty) -> GlobalValue<'v> {
        GlobalValue {
            value: None,
            ty,
            as_type: None,
            approximation: None,
        }
    }

    fn approximated(approximation: DeclarationApproximation) -> GlobalValue<'v> {
        GlobalValue {
            approximation: Some(approximation),
            ..GlobalValue::any()
        }
    }

    /// The value to use where a type is expected: the value, or the type a
    /// loaded name denotes.
    fn type_operand(&self, heap: Heap<'v>) -> Option<Value<'v>> {
        match (self.value, &self.as_type) {
            (Some(value), _) => Some(value),
            (None, Some(ty)) => Some(TypeCompiled::from_ty(ty, heap).to_inner()),
            (None, None) => None,
        }
    }

    /// The type this name denotes in a type annotation, when it is a type:
    /// its value's, or the one a loaded name carries.
    fn denoted_type(&self, heap: Heap<'v>) -> Option<Ty> {
        match (self.value, &self.as_type) {
            (Some(value), _) => Some(TypeCompiled::new(value, heap).ok()?.as_ty().clone()),
            (None, as_type) => as_type.clone(),
        }
    }
}

/// `record`, `field` or `enum` as starlark defines them: the native, found by
/// its mark, never by its name.
fn declaration_native(value: Value) -> Option<SpecialBuiltinFunction> {
    match value
        .downcast_ref::<NativeFunction>()?
        .special_builtin_function
    {
        Some(
            mark @ (SpecialBuiltinFunction::Record
            | SpecialBuiltinFunction::Field
            | SpecialBuiltinFunction::Enum),
        ) => Some(mark),
        _ => None,
    }
}

struct GlobalTypesBuilder<'a, 'v> {
    approximations: &'a mut Vec<Approximation>,
    heap: Heap<'v>,
    values: UnorderedMap<ModuleSlotId, GlobalValue<'v>>,
    /// Each binding of a record or enum declaration typed as `Any`, and why.
    declaration_approximations: UnorderedMap<BindingId, DeclarationApproximation>,
    errors: Vec<TypingError>,
    module_scope_data: &'a ModuleScopeData<'a>,
    ctx: TypingOracleCtx<'a>,
}

impl<'a, 'v> GlobalTypesBuilder<'a, 'v> {
    fn internal_error(&self, span: Span, message: impl Display) -> InternalError {
        InternalError::msg(message, span, self.ctx.codemap)
    }

    fn err(&mut self, span: Span, e: crate::Error) -> GlobalValue<'v> {
        self.errors
            .push(TypingError::new(e, span, self.ctx.codemap));
        GlobalValue::any()
    }

    fn call(
        &mut self,
        span: Span,
        f: &CstExpr,
        args: &CallArgsP<CstPayload>,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let callee = self.expr(f)?;
        match callee.value.and_then(declaration_native) {
            Some(SpecialBuiltinFunction::Record) => self.record(args),
            Some(SpecialBuiltinFunction::Field) => self.field(args),
            Some(SpecialBuiltinFunction::Enum) => self.enumeration(args),
            _ => self.call_result(span, &callee.ty),
        }
    }

    /// The type of a call to `callee` with arguments the pre-pass does not
    /// look at: what the oracle gives a call with `*Any` and `**Any`, which no
    /// signature rejects. The call is never run and its arguments are never
    /// checked, so the result has a type and never a value.
    fn call_result(&self, span: Span, callee: &Ty) -> Result<GlobalValue<'v>, InternalError> {
        let any = Spanned {
            span,
            node: Ty::any(),
        };
        let args = TyCallArgs {
            pos: Vec::new(),
            named: Vec::new(),
            args: Some(any.clone()),
            kwargs: Some(any),
        };
        match self.ctx.validate_call(span, callee, &args) {
            Ok(ty) => Ok(GlobalValue::ty(ty)),
            Err(TypingOrInternalError::Typing(_)) => Ok(GlobalValue::any()),
            Err(TypingOrInternalError::Internal(e)) => Err(e),
        }
    }

    /// The field a `record(...)` argument declares, from the argument's value
    /// or the type a loaded name denotes, never from its `ty`: a value that
    /// is only typed (`a = make()`) is unknown.
    fn record_field(&self, arg: &GlobalValue<'v>) -> FieldGen<Value<'v>> {
        let typ = match arg.type_operand(self.heap) {
            Some(value) => {
                if let Some(field) = Field::from_value(value) {
                    return field.dupe();
                }
                // Not a type: evaluation rejects it, so lint asks nothing of it.
                match TypeCompiled::new(value, self.heap) {
                    Ok(typ) => typ,
                    Err(_) => return self.optional_any_field(),
                }
            }
            None => return self.optional_any_field(),
        };
        FieldGen::new(typ, None)
    }

    /// A field lint knows nothing of: any type, and never required.
    fn optional_any_field(&self) -> FieldGen<Value<'v>> {
        FieldGen::new(
            TypeCompiled::from_ty(&Ty::any(), self.heap),
            Some(Value::new_none()),
        )
    }

    /// `record(name = type_or_field, ...)`, built as the native builds it.
    fn record(&mut self, args: &CallArgsP<CstPayload>) -> Result<GlobalValue<'v>, InternalError> {
        let mut named = Vec::with_capacity(args.args.len());
        for arg in &args.args {
            match &arg.node {
                ArgumentP::Named(name, value) => named.push((name, value)),
                ArgumentP::Args(_) | ArgumentP::KwArgs(_) => {
                    return Ok(GlobalValue::approximated(
                        DeclarationApproximation::StarArgs,
                    ));
                }
                ArgumentP::Positional(_) => {
                    return Ok(GlobalValue::approximated(
                        DeclarationApproximation::InvalidDeclaration,
                    ));
                }
            }
        }
        if named.is_empty() {
            return Ok(GlobalValue::approximated(
                DeclarationApproximation::InvalidDeclaration,
            ));
        }
        let mut fields = SmallMap::with_capacity(named.len());
        for (name, value) in named {
            let value = self.expr(value)?;
            let field = self.record_field(&value);
            if fields.insert(name.node.clone(), field).is_some() {
                return Ok(GlobalValue::approximated(
                    DeclarationApproximation::InvalidDeclaration,
                ));
            }
        }
        Ok(GlobalValue::value(self.heap.alloc(RecordType::new(fields))))
    }

    /// `field(type, default = ...)`, built as the native builds it. An
    /// unknown type is `Any`. A default lint cannot tell anything about makes
    /// the field optional `Any`: lint never requires what evaluation does not.
    fn field(&mut self, args: &CallArgsP<CstPayload>) -> Result<GlobalValue<'v>, InternalError> {
        let mut typ = None;
        let mut default = None;
        for arg in &args.args {
            match &arg.node {
                ArgumentP::Positional(x) if typ.is_none() => typ = Some(x),
                ArgumentP::Positional(x) if default.is_none() => default = Some(x),
                ArgumentP::Named(name, x) if name.node == "default" && default.is_none() => {
                    default = Some(x)
                }
                ArgumentP::Args(_) | ArgumentP::KwArgs(_) => return Ok(GlobalValue::any()),
                ArgumentP::Positional(_) | ArgumentP::Named(..) => {
                    return Ok(GlobalValue::any());
                }
            }
        }
        let Some(typ) = typ else {
            return Ok(GlobalValue::any());
        };
        let typ = self.expr(typ)?;
        let typ = match typ.type_operand(self.heap) {
            Some(value) => match TypeCompiled::new(value, self.heap) {
                Ok(typ) => typ,
                Err(_) => TypeCompiled::from_ty(&Ty::any(), self.heap),
            },
            None => TypeCompiled::from_ty(&Ty::any(), self.heap),
        };
        let field = match default {
            None => FieldGen::new(typ, None),
            Some(default) => {
                let known = Self::is_known_default(default);
                match self.expr(default)?.value {
                    Some(value) => FieldGen::new(typ, Some(value)),
                    // Lint never reads a default's value, only its presence.
                    None if known => FieldGen::new(typ, Some(Value::new_none())),
                    None => self.optional_any_field(),
                }
            }
        };
        Ok(GlobalValue::value(self.heap.alloc(field)))
    }

    /// A default the pre-pass does not evaluate, but whose value is a literal
    /// or a display, so the field's own type stands for it.
    fn is_known_default(default: &CstExpr) -> bool {
        match &default.node {
            ExprP::Literal(_)
            | ExprP::FString(_)
            | ExprP::List(_)
            | ExprP::Dict(_)
            | ExprP::Tuple(_)
            | ExprP::ListComprehension(..)
            | ExprP::DictComprehension(..) => true,
            ExprP::Minus(x) | ExprP::Plus(x) => Self::is_known_default(x),
            _ => false,
        }
    }

    /// `enum("a", "b", ...)`, built as the native builds it, when every
    /// variant is a string literal.
    fn enumeration(
        &mut self,
        args: &CallArgsP<CstPayload>,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let mut variants = Vec::with_capacity(args.args.len());
        let mut approximation = None;
        for arg in &args.args {
            match &arg.node {
                ArgumentP::Positional(x) => match &x.node {
                    ExprP::Literal(AstLiteral::String(s)) => {
                        variants.push(self.heap.alloc_str(s.node.as_str()))
                    }
                    _ => {
                        approximation.get_or_insert(DeclarationApproximation::NonLiteralVariant);
                    }
                },
                ArgumentP::Args(_) | ArgumentP::KwArgs(_) => {
                    return Ok(GlobalValue::approximated(
                        DeclarationApproximation::StarArgs,
                    ));
                }
                ArgumentP::Named(..) => {
                    approximation = Some(DeclarationApproximation::InvalidDeclaration);
                }
            }
        }
        if let Some(approximation) = approximation {
            return Ok(GlobalValue::approximated(approximation));
        }
        if variants.is_empty() {
            return Ok(GlobalValue::approximated(
                DeclarationApproximation::InvalidDeclaration,
            ));
        }
        match EnumType::new(variants, self.heap) {
            Ok(enum_type) => Ok(GlobalValue::value(enum_type.to_value())),
            // A duplicate variant.
            Err(_) => Ok(GlobalValue::approximated(
                DeclarationApproximation::InvalidDeclaration,
            )),
        }
    }

    /// The declaration native `f` is, when it is an identifier bound to one.
    /// Reads no local slot and records no error, so it is safe on code the
    /// pre-pass does not evaluate (conditional code, def bodies).
    fn callee_declaration_native(&self, f: &CstExpr) -> Option<SpecialBuiltinFunction> {
        let ExprP::Identifier(ident) = &f.node else {
            return None;
        };
        let value = match ident.payload.as_ref()? {
            ResolvedIdent::Slot(Slot::Module(slot), _) => self.values.get(slot)?.value?,
            ResolvedIdent::Slot(Slot::Local(_), _) => return None,
            ResolvedIdent::Global(g) => g.to_value(),
        };
        declaration_native(value)
    }

    /// Whether `expr` declares a record or enum type.
    fn is_type_declaration(&self, expr: &CstExpr) -> bool {
        match &expr.node {
            ExprP::Call(f, _) => matches!(
                self.callee_declaration_native(f),
                Some(SpecialBuiltinFunction::Record | SpecialBuiltinFunction::Enum)
            ),
            _ => false,
        }
    }

    fn approximate_declaration(
        &mut self,
        ident: &CstAssignIdent,
        approximation: DeclarationApproximation,
    ) -> Result<(), InternalError> {
        let binding_id = ident.resolved_binding_id(self.ctx.codemap)?;
        self.declaration_approximations
            .insert(binding_id, approximation);
        Ok(())
    }

    /// Record each record or enum declared in a def body: the pre-pass does
    /// not evaluate def bodies, so it is `Any` there.
    fn def_declarations(&mut self, stmt: &CstStmt) -> Result<(), InternalError> {
        match &stmt.node {
            StmtP::Assign(AssignP { lhs, rhs, .. }) => {
                if let AssignTargetP::Identifier(ident) = &lhs.node {
                    if self.is_type_declaration(rhs) {
                        self.approximate_declaration(ident, DeclarationApproximation::InDef)?;
                    }
                }
                Ok(())
            }
            StmtP::Statements(xs) => {
                for x in xs {
                    self.def_declarations(x)?;
                }
                Ok(())
            }
            StmtP::If(_, body) => self.def_declarations(body),
            StmtP::IfElse(_, then_else) => {
                let (then_block, else_block) = &**then_else;
                self.def_declarations(then_block)?;
                self.def_declarations(else_block)
            }
            StmtP::For(ForP { body, .. }) => self.def_declarations(body),
            StmtP::Def(def) => self.def_declarations(&def.body),
            StmtP::Break
            | StmtP::Continue
            | StmtP::Pass
            | StmtP::Return(_)
            | StmtP::Expression(_)
            | StmtP::AssignModify(..)
            | StmtP::Load(_) => Ok(()),
        }
    }

    fn expr_ident(&self, ident: &CstIdent) -> Result<GlobalValue<'v>, InternalError> {
        let Some(resolved_ident) = &ident.payload else {
            return Err(self.internal_error(ident.span, "unresolved ident"));
        };
        match resolved_ident {
            ResolvedIdent::Slot(Slot::Module(module_slot_id), _) => {
                match self.values.get(module_slot_id) {
                    None => Ok(GlobalValue::any()),
                    Some(v) => Ok(v.clone()),
                }
            }
            ResolvedIdent::Slot(Slot::Local(_), _) => {
                Err(self.internal_error(ident.span, "local slot in global scope"))
            }
            ResolvedIdent::Global(g) => Ok(GlobalValue::value(g.to_value())),
        }
    }

    fn expr_literal(&mut self, literal: &AstLiteral) -> Result<GlobalValue<'v>, InternalError> {
        match literal {
            AstLiteral::String(s) => Ok(GlobalValue::value(self.heap.alloc(s.node.as_str()))),
            // Not used in type expressions.
            _ => Ok(GlobalValue::any()),
        }
    }

    fn tuple(&mut self, xs: &[CstExpr]) -> Result<GlobalValue<'v>, InternalError> {
        let xs = xs.try_map(|x| self.expr_spanned(x))?;
        if let Ok(xs) = xs.try_map(|v| v.value.ok_or(())) {
            Ok(GlobalValue::value(self.heap.alloc(AllocTuple(xs))))
        } else {
            Ok(GlobalValue::any())
        }
    }

    fn dot(
        &mut self,
        span: Span,
        object: &CstExpr,
        field: &AstString,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let object = self.expr(object)?;
        if let Some(value) = object.value {
            match value.get_attr_error(field.as_str(), self.heap) {
                // A bound method has no type of its own: it has the type the
                // checker gives the attribute, so a call of it
                // (`"a,b".split(",")`) has the method's return type.
                Ok(v) if v.downcast_ref::<BoundMethod>().is_some() => {
                    let ty = self
                        .ctx
                        .expr_dot(span, &object.ty, field.as_str())
                        .unwrap_or_else(|_| Ty::of_value(v));
                    Ok(GlobalValue {
                        ty,
                        ..GlobalValue::value(v)
                    })
                }
                Ok(v) => Ok(GlobalValue::value(v)),
                Err(e) => Ok(self.err(span, e)),
            }
        } else {
            Ok(GlobalValue::any())
        }
    }

    fn index(
        &mut self,
        span: Span,
        array: &CstExpr,
        index: &CstExpr,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let array = self.expr(array)?;
        let index = self.expr(index)?;
        if let (Some(array), Some(index)) = (array.value, index.type_operand(self.heap)) {
            match array.at(index, self.heap) {
                Ok(value) => Ok(GlobalValue::value(value)),
                Err(e) => Ok(self.err(span, e)),
            }
        } else {
            Ok(GlobalValue::any())
        }
    }

    fn index2(
        &mut self,
        span: Span,
        array: &CstExpr,
        index0: &CstExpr,
        index1: &CstExpr,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let array = self.expr(array)?;
        let index0 = self.expr(index0)?;
        let index1 = self.expr(index1)?;
        if let (Some(array), Some(index0), Some(index1)) = (
            array.value,
            index0.type_operand(self.heap),
            index1.type_operand(self.heap),
        ) {
            match array.get_ref().at2(index0, index1, self.heap) {
                Ok(value) => Ok(GlobalValue::value(value)),
                Err(e) => Ok(self.err(span, e)),
            }
        } else {
            Ok(GlobalValue::any())
        }
    }

    fn bin_op(
        &mut self,
        span: Span,
        lhs: &CstExpr,
        op: BinOp,
        rhs: &CstExpr,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let lhs = self.expr(lhs)?;
        let rhs = self.expr(rhs)?;
        if let (Some(lhs), BinOp::BitOr, Some(rhs)) =
            (lhs.type_operand(self.heap), op, rhs.type_operand(self.heap))
        {
            match lhs.bit_or(rhs, self.heap) {
                Ok(value) => Ok(GlobalValue::value(value)),
                Err(e) => Ok(self.err(span, e)),
            }
        } else {
            Ok(GlobalValue::any())
        }
    }

    fn expr(&mut self, expr: &CstExpr) -> Result<GlobalValue<'v>, InternalError> {
        let span = expr.span;
        match &expr.node {
            ExprP::Tuple(xs) => self.tuple(xs),
            ExprP::Dot(object, field) => self.dot(span, object, field),
            ExprP::Call(f, args) => self.call(span, f, args),
            ExprP::Index(a_i) => {
                let (a, i) = &**a_i;
                self.index(span, a, i)
            }
            ExprP::Index2(a_i0_i1) => {
                let (a, i0, i1) = &**a_i0_i1;
                self.index2(span, a, i0, i1)
            }
            ExprP::Identifier(ident) => self.expr_ident(ident),
            ExprP::Literal(lit) => self.expr_literal(lit),
            ExprP::Op(lhs, op, rhs) => self.bin_op(span, lhs, *op, rhs),
            // These are not used in type expressions.
            ExprP::Slice(..)
            | ExprP::Lambda(_)
            | ExprP::Not(..)
            | ExprP::Minus(..)
            | ExprP::Plus(..)
            | ExprP::BitNot(..)
            | ExprP::If(..)
            | ExprP::List(_)
            | ExprP::Dict(_)
            | ExprP::ListComprehension(_, _, _)
            | ExprP::DictComprehension(_, _, _)
            | ExprP::FString(_) => Ok(GlobalValue::any()),
        }
    }

    fn expr_spanned(&mut self, expr: &CstExpr) -> Result<Spanned<GlobalValue<'v>>, InternalError> {
        let value = self.expr(expr)?;
        Ok(Spanned {
            span: expr.span,
            node: value,
        })
    }

    fn load(&mut self, load: &LoadP<CstPayload>) -> Result<(), InternalError> {
        for LoadArgP { local, their, .. } in &load.args {
            let ty = load.payload.get(their).cloned().unwrap_or_else(Ty::any);
            let value = GlobalValue {
                as_type: load.payload.get_type(their).cloned(),
                ..GlobalValue::ty(ty)
            };
            self.assign_ident_value(local, value)?;
        }
        Ok(())
    }

    fn resolve_assign_ident_to_module_slot_id(
        &self,
        ident: &CstAssignIdent,
    ) -> Result<ModuleSlotId, InternalError> {
        let binding_id = ident.resolved_binding_id(self.ctx.codemap)?;
        let binding = self.module_scope_data.get_binding(binding_id);
        let resolved_slot = binding.resolved_slot(self.ctx.codemap)?;
        match resolved_slot {
            Slot::Module(slot_id) => Ok(slot_id),
            Slot::Local(_) => Err(self.internal_error(ident.span, "local slot")),
        }
    }

    /// Name a record or enum type bound to `ident`, as `export_as` does at
    /// evaluation, and type the binding with its now named type.
    fn export(
        &self,
        ident: &CstAssignIdent,
        value: GlobalValue<'v>,
    ) -> Result<GlobalValue<'v>, InternalError> {
        let Some(v) = value.value else {
            return Ok(value);
        };
        let named = if let Some(record) = v.downcast_ref::<RecordType>() {
            record.init_ty(&ident.ident)
        } else if let Some(enum_type) = v.downcast_ref::<EnumType>() {
            enum_type.init_ty(&ident.ident)
        } else {
            return Ok(value);
        };
        named.map_err(|e| InternalError::from_error(e, ident.span, self.ctx.codemap))?;
        Ok(GlobalValue::value(v))
    }

    fn assign_ident_value(
        &mut self,
        ident: &CstAssignIdent,
        value: GlobalValue<'v>,
    ) -> Result<(), InternalError> {
        let module_slot_id = self.resolve_assign_ident_to_module_slot_id(ident)?;
        let value = self.export(ident, value)?;
        let value = match self.values.entry(module_slot_id) {
            unordered_map::Entry::Occupied(mut e) => {
                let value = GlobalValue::union2(value, e.get().clone());
                e.insert(value.clone());
                value
            }
            unordered_map::Entry::Vacant(e) => {
                e.insert(value.clone());
                value
            }
        };
        if let Some(approximation) = value.approximation {
            self.approximate_declaration(ident, approximation)?;
        }
        Ok(())
    }

    fn assign_unset_ident(&mut self, target: &CstAssignIdent) -> Result<(), InternalError> {
        let module_slot_id = self.resolve_assign_ident_to_module_slot_id(target)?;
        let was_declaration = self
            .values
            .get(&module_slot_id)
            .is_some_and(|v| v.is_declaration());
        let value = if was_declaration {
            self.approximate_declaration(target, DeclarationApproximation::ConditionalBinding)?;
            GlobalValue::approximated(DeclarationApproximation::ConditionalBinding)
        } else {
            GlobalValue::any()
        };
        self.values.insert(module_slot_id, value);
        Ok(())
    }

    /// `target = rhs` where the pre-pass does not know whether it runs.
    fn assign_unset_conditional(
        &mut self,
        target: &AssignTargetP<CstPayload>,
        rhs: &CstExpr,
    ) -> Result<(), InternalError> {
        if let AssignTargetP::Identifier(ident) = target {
            if self.is_type_declaration(rhs) {
                let module_slot_id = self.resolve_assign_ident_to_module_slot_id(ident)?;
                self.approximate_declaration(ident, DeclarationApproximation::ConditionalBinding)?;
                self.values.insert(
                    module_slot_id,
                    GlobalValue::approximated(DeclarationApproximation::ConditionalBinding),
                );
                return Ok(());
            }
        }
        self.assign_unset(target)
    }

    fn assign_value(
        &mut self,
        lhs: &AssignTargetP<CstPayload>,
        rhs: GlobalValue<'v>,
    ) -> Result<(), InternalError> {
        match lhs {
            AssignTargetP::Tuple(xs) => {
                // TODO(nga): do better if RHS is a tuple.
                for x in xs {
                    self.assign_unset(x)?;
                }
                Ok(())
            }
            AssignTargetP::Index(_) => Ok(()),
            AssignTargetP::Dot(_, _) => Ok(()),
            AssignTargetP::Identifier(ident) => self.assign_ident_value(ident, rhs),
        }
    }

    fn assign(
        &mut self,
        lhs: &AssignTargetP<CstPayload>,
        rhs: &CstExpr,
    ) -> Result<(), InternalError> {
        let rhs = self.expr(rhs)?;
        self.assign_value(lhs, rhs)
    }

    /// Unset the variables.
    ///
    /// When evaluating code like:
    ///
    /// ```python
    /// if x:
    ///   a = list
    /// else:
    ///   b = int
    /// ```
    ///
    /// We don't know what branch is taken. So we just unset both `a` and `b`.
    fn assign_unset(&mut self, lhs: &AssignTargetP<CstPayload>) -> Result<(), InternalError> {
        match lhs {
            AssignTargetP::Tuple(xs) => {
                for x in xs {
                    self.assign_unset(x)?;
                }
                Ok(())
            }
            AssignTargetP::Index(..) => Ok(()),
            AssignTargetP::Dot(..) => Ok(()),
            AssignTargetP::Identifier(ident) => self.assign_unset_ident(ident),
        }
    }

    fn assign_stmt(&mut self, assign: &AssignP<CstPayload>) -> Result<(), InternalError> {
        let AssignP { lhs, ty, rhs } = assign;
        match ty {
            None => self.assign(lhs, rhs),
            Some(_ty) => {
                // TODO(nga): do not ignore type.
                self.assign(lhs, rhs)
            }
        }
    }

    fn for_stmt_unset(&mut self, for_stmt: &ForP<CstPayload>) -> Result<(), InternalError> {
        let ForP { var, over: _, body } = for_stmt;
        self.assign_unset(var)?;
        self.eval_stmt_unset(body)
    }

    /// When we are not sure if code is executed exactly once (like in a for loop body),
    /// we just reset all the variables.
    fn eval_stmt_unset(&mut self, stmt: &CstStmt) -> Result<(), InternalError> {
        match &stmt.node {
            StmtP::Break => Ok(()),
            StmtP::Continue => Ok(()),
            StmtP::Pass => Ok(()),
            StmtP::Return(_) => return Err(self.internal_error(stmt.span, "return")),
            StmtP::Expression(_) => Ok(()),
            StmtP::Assign(AssignP { lhs, rhs, .. }) => self.assign_unset_conditional(lhs, rhs),
            StmtP::AssignModify(lhs, _, _) => self.assign_unset(lhs),
            StmtP::Statements(xs) => {
                for x in xs {
                    self.eval_stmt_unset(x)?;
                }
                Ok(())
            }
            StmtP::If(_cond, then_block) => self.eval_stmt_unset(then_block),
            StmtP::IfElse(_cond, then_else) => {
                let (then_block, else_block) = &**then_else;
                self.eval_stmt_unset(then_block)?;
                self.eval_stmt_unset(else_block)?;
                Ok(())
            }
            StmtP::For(for_stmt) => self.for_stmt_unset(for_stmt),
            StmtP::Def(def) => {
                self.def_declarations(&def.body)?;
                self.assign_unset_ident(&def.name)
            }
            StmtP::Load(_) => Err(self.internal_error(stmt.span, "load")),
        }
    }

    fn top_level_def(&mut self, def: &DefP<CstPayload>) -> Result<(), InternalError> {
        let DefParams {
            params: def_params,
            indices: _,
        } = DefParams::unpack(&def.params, self.ctx.codemap)
            .map_err(InternalError::from_eval_exception)?;

        let mut pos_only = Vec::new();
        let mut pos_or_name = Vec::new();
        let mut args = None;
        let mut name_only = Vec::new();
        let mut kwargs = None;

        for param in def_params {
            let ty = match (param.ty, &param.kind) {
                (None, DefParamKind::Regular(_, Some(default))) => {
                    literal_default_ty(default).unwrap_or_else(Ty::any)
                }
                (ty, _) => self.get_ty_expr_opt(ty)?,
            };
            match param.kind {
                DefParamKind::Regular(mode, default_value) => {
                    let name = param.ident.ident.as_str();
                    let required = match default_value.is_some() {
                        true => ParamIsRequired::No,
                        false => ParamIsRequired::Yes,
                    };
                    match mode {
                        DefRegularParamMode::PosOnly => pos_only.push((required, ty)),
                        DefRegularParamMode::PosOrName => {
                            pos_or_name.push((ArcStr::from(name), required, ty))
                        }
                        DefRegularParamMode::NameOnly => {
                            name_only.push((ArcStr::from(name), required, ty))
                        }
                    };
                }
                DefParamKind::Args => args = Some(ty),
                DefParamKind::Kwargs => kwargs = Some(ty),
            }
        }

        self.def_declarations(&def.body)?;

        let result = self.get_ty_expr_opt(def.return_type.as_deref())?;

        let params = ParamSpec::new_parts(pos_only, pos_or_name, args, name_only, kwargs)
            .map_err(|e| InternalError::from_error(e, def.signature_span(), self.ctx.codemap))?;

        self.assign_ident_value(&def.name, GlobalValue::ty(Ty::function(params, result)))
    }

    fn eval_stmt(&mut self, stmt: &CstStmt) -> Result<(), InternalError> {
        let span = stmt.span;
        match &stmt.node {
            StmtP::Break => Err(self.internal_error(span, "top-level break")),
            StmtP::Continue => Err(self.internal_error(span, "top-level continue")),
            StmtP::Pass => Ok(()),
            StmtP::Return(_) => Err(self.internal_error(span, "top-level return")),
            StmtP::Expression(_) => Ok(()),
            StmtP::Assign(assign) => self.assign_stmt(assign),
            StmtP::AssignModify(..) => Ok(()),
            StmtP::Statements(_) => {
                Err(self.internal_error(span, "statements in top-level statement"))
            }
            StmtP::If(_cond, th) => self.eval_stmt_unset(th),
            StmtP::IfElse(_cond, th_el) => {
                let (th, el) = &**th_el;
                self.eval_stmt_unset(th)?;
                self.eval_stmt_unset(el)?;
                Ok(())
            }
            StmtP::For(for_stmt) => self.for_stmt_unset(for_stmt),
            StmtP::Def(def) => self.top_level_def(def),
            StmtP::Load(load) => self.load(load),
        }
    }

    fn unknown_ty(&mut self, span: Span) -> Ty {
        self.approximations
            .push(Approximation::new("Unknown type", span));
        Ty::any()
    }

    fn eval_path(
        &mut self,
        path: &TypePathP<CstPayload>,
    ) -> Result<Option<Value<'v>>, InternalError> {
        let TypePathP { first, rem } = path;
        let Some(mut value) = self.expr_ident(first)?.value else {
            return Ok(None);
        };
        for x in rem {
            match value.get_attr_error(x, self.heap) {
                Ok(v) => value = v,
                Err(e) => {
                    let span = first.span.merge(x.span);
                    self.errors
                        .push(TypingError::new(e, span, self.ctx.codemap));
                    return Ok(None);
                }
            }
        }
        Ok(Some(value))
    }

    fn try_proper_ty(&mut self, path: &TypePathP<CstPayload>) -> Result<Option<Ty>, InternalError> {
        let TypePathP { first, rem } = path;
        if rem.is_empty() {
            // A loaded record, enum or alias.
            if let GlobalValue {
                value: None,
                as_type: Some(ty),
                ..
            } = self.expr_ident(first)?
            {
                return Ok(Some(ty));
            }
        }
        let Some(value) = self.eval_path(path)? else {
            return Ok(None);
        };
        match TypeCompiled::new(value, self.heap) {
            Ok(ty) => Ok(Some(ty.as_ty().clone())),
            Err(e) => {
                let span =
                    Span::merge_all(iter::once(first.span).chain(rem.iter().map(|x| x.span)));
                self.errors
                    .push(TypingError::new_anyhow(e, span, self.ctx.codemap));
                Ok(None)
            }
        }
    }

    fn path_ty(&mut self, path: &TypePathP<CstPayload>) -> Result<Ty, InternalError> {
        let TypePathP { first, rem } = path;
        if let Some(ty) = self.try_proper_ty(path)? {
            return Ok(ty);
        }

        let span = Span::merge_all(iter::once(first.span).chain(rem.iter().map(|x| x.span)));
        Ok(self.unknown_ty(span))
    }

    fn from_type_expr_impl(
        &mut self,
        x: &Spanned<TypeExprUnpackP<CstPayload>>,
    ) -> Result<Ty, InternalError> {
        match &x.node {
            TypeExprUnpackP::Ellipsis => {
                self.approximations
                    .push(Approximation::new("Ellipsis cannot be used as type", x));
                Ok(Ty::any())
            }
            TypeExprUnpackP::List(..) => {
                self.approximations.push(Approximation::new(
                    "List literal [...] cannot be used as type",
                    x,
                ));
                Ok(Ty::any())
            }
            TypeExprUnpackP::Tuple(xs) => {
                Ok(Ty::tuple(xs.try_map(|x| self.from_type_expr_impl(x))?))
            }
            TypeExprUnpackP::Union(xs) => {
                Ok(Ty::unions(xs.try_map(|x| self.from_type_expr_impl(x))?))
            }
            TypeExprUnpackP::Path(path) => self.path_ty(path),
            TypeExprUnpackP::Index(a, i) => {
                let i = self.from_type_expr_impl(i)?;
                match self.expr_ident(a)?.value {
                    Some(a) => {
                        // Built-in generic types (list, set) are special-cased because they
                        // are functions, not types, so they lack eval_type(). Their
                        // parameterization is handled directly via Ty constructors.
                        if a.ptr_eq(Constants::get().fn_list.0.to_value()) {
                            Ok(Ty::list(i))
                        } else {
                            let i_compiled = TypeCompiled::from_ty(&i, self.heap);
                            match a.get_ref().at(i_compiled.to_inner(), self.heap) {
                                Ok(t) => match TypeCompiled::new(t, self.heap) {
                                    Ok(ty) => Ok(ty.as_ty().clone()),
                                    Err(_) => {
                                        self.approximations.push(Approximation::new(
                                            "TypeCompiled::new failed",
                                            x,
                                        ));
                                        Ok(Ty::any())
                                    }
                                },
                                Err(e) => {
                                    self.approximations.push(Approximation::new(
                                        "Type parameterization failed",
                                        e,
                                    ));
                                    Ok(Ty::any())
                                }
                            }
                        }
                    }
                    _ => {
                        self.approximations
                            .push(Approximation::new("Not global", x));
                        Ok(Ty::any())
                    }
                }
            }
            TypeExprUnpackP::Index2(a, i0, i1) => {
                if let Some(a) = self.eval_path(a)? {
                    if a.ptr_eq(Constants::get().fn_dict.0.to_value()) {
                        let i0 = self.from_type_expr_impl(i0)?;
                        let i1 = self.from_type_expr_impl(i1)?;
                        let i0 = TypeCompiled::from_ty(&i0, self.heap);
                        let i1 = TypeCompiled::from_ty(&i1, self.heap);
                        match a.get_ref().at2(i0.to_inner(), i1.to_inner(), self.heap) {
                            Ok(t) => match TypeCompiled::new(t, self.heap) {
                                Ok(ty) => Ok(ty.as_ty().clone()),
                                Err(_) => {
                                    self.approximations
                                        .push(Approximation::new("TypeCompiled::new failed", x));
                                    Ok(Ty::any())
                                }
                            },
                            Err(e) => {
                                self.approximations
                                    .push(Approximation::new("Getitem2 failed", e));
                                Ok(Ty::any())
                            }
                        }
                    } else if a.ptr_eq(Constants::get().fn_tuple.0.to_value()) {
                        let i0 = self.from_type_expr_impl(i0)?;
                        let TypeExprUnpackP::Ellipsis = i1.node else {
                            self.approximations
                                .push(Approximation::new("Expecting ellipsis in tuple[x, ...]", x));
                            return Ok(Ty::any());
                        };
                        let r0 = TypeCompiled::from_ty(&i0, self.heap);
                        match a.get_ref().at2(
                            r0.to_inner(),
                            Ellipsis::new_value().to_value(),
                            self.heap,
                        ) {
                            Ok(t) => match TypeCompiled::new(t, self.heap) {
                                Ok(ty) => Ok(ty.as_ty().clone()),
                                Err(_) => {
                                    self.approximations
                                        .push(Approximation::new("TypeCompiled::new failed", x));
                                    Ok(Ty::any())
                                }
                            },
                            Err(e) => {
                                self.approximations
                                    .push(Approximation::new("Getitem2 failed", e));
                                Ok(Ty::any())
                            }
                        }
                    } else if a.ptr_eq(Constants::get().typing_callable.0.to_value()) {
                        let TypeExprUnpackP::List(items) = &i0.node else {
                            self.approximations.push(Approximation::new(
                                "Expecting list in Callable[[...], ...]",
                                x,
                            ));
                            return Ok(Ty::any());
                        };
                        let args = items.try_map(|x| {
                            Ok(
                                TypeCompiled::from_ty(&self.from_type_expr_impl(x)?, self.heap)
                                    .to_inner(),
                            )
                        })?;
                        let args = self.heap.alloc_list(&args);
                        let ret = self.from_type_expr_impl(i1)?;
                        let ret = TypeCompiled::from_ty(&ret, self.heap).to_inner();
                        match a.get_ref().at2(args, ret, self.heap) {
                            Ok(t) => match TypeCompiled::new(t, self.heap) {
                                Ok(ty) => Ok(ty.as_ty().clone()),
                                Err(_) => {
                                    self.approximations
                                        .push(Approximation::new("TypeCompiled::new failed", x));
                                    Ok(Ty::any())
                                }
                            },
                            Err(e) => {
                                self.approximations
                                    .push(Approximation::new("Getitem2 failed", e));
                                Ok(Ty::any())
                            }
                        }
                    } else {
                        self.approximations
                            .push(Approximation::new("Not dict or tuple", x));
                        return Ok(Ty::any());
                    }
                } else {
                    self.approximations
                        .push(Approximation::new("Not global", x));
                    Ok(Ty::any())
                }
            }
        }
    }

    fn ty_expr(&mut self, expr: &CstTypeExpr) -> Result<Ty, InternalError> {
        let x = TypeExprUnpackP::unpack(&expr.expr, self.ctx.codemap)
            .map_err(InternalError::from_diagnostic)?;
        self.from_type_expr_impl(&x)
    }

    fn get_ty_expr(&self, expr: &CstTypeExpr) -> Result<Ty, InternalError> {
        match &expr.payload.typechecker_ty {
            Some(ty) => Ok(ty.clone()),
            None => Err(self.internal_error(expr.span, "type not set")),
        }
    }

    fn get_ty_expr_opt(&mut self, expr: Option<&CstTypeExpr>) -> Result<Ty, InternalError> {
        match expr {
            None => Ok(Ty::any()),
            Some(expr) => self.get_ty_expr(expr),
        }
    }

    fn fill_types(&mut self, stmt: &mut CstStmt) -> Result<(), InternalError> {
        stmt.visit_type_expr_err_mut(&mut |type_expr| {
            if type_expr.payload.typechecker_ty.is_some() {
                return Err(self.internal_error(type_expr.span, "type already set"));
            }
            type_expr.payload.typechecker_ty = Some(self.ty_expr(type_expr)?);
            Ok(())
        })
    }

    fn top_level_stmt(&mut self, stmt: &mut CstStmt) -> Result<(), InternalError> {
        // Fill all type payloads.
        self.fill_types(stmt)?;
        // Partially evaluate expressions which can be used in the following type expressions.
        self.eval_stmt(stmt)
    }
}

/// Types of module-level variables.
#[derive(Default)]
pub(crate) struct ModuleVarTypes {
    pub(crate) types: UnorderedMap<ModuleSlotId, Ty>,
    /// The type each module-level name that is a type (a record, an enum or
    /// an alias such as `Names = list[str]`) denotes in a type annotation:
    /// from its value, or, for a loaded name, from its module's interface.
    pub(crate) as_types: UnorderedMap<ModuleSlotId, Ty>,
    /// Each binding of a record or enum declaration the pre-pass types as
    /// `Any`, top-level or in a def, and why.
    pub(crate) declaration_approximations: UnorderedMap<BindingId, DeclarationApproximation>,
}

/// Populate `TypeExprP` type payload when running lint typechecker.
/// (Compiler typechecked populates the payload after proper full evaluation.)
pub(crate) fn fill_types_for_lint_typechecker(
    module: &mut [&mut CstStmt],
    ctx: TypingOracleCtx,
    module_scope_data: &ModuleScopeData,
    approximations: &mut Vec<Approximation>,
) -> Result<(Vec<TypingError>, ModuleVarTypes), InternalError> {
    Heap::temp(|heap| {
        let mut builder = GlobalTypesBuilder {
            heap,
            ctx,
            values: UnorderedMap::new(),
            declaration_approximations: UnorderedMap::new(),
            errors: Vec::new(),
            module_scope_data,
            approximations,
        };
        for stmt in module.iter_mut() {
            builder.top_level_stmt(stmt)?;
        }
        let GlobalTypesBuilder {
            errors,
            values,
            declaration_approximations,
            ..
        } = builder;
        let as_types = values
            .entries_unordered()
            .filter_map(|(slot, v)| Some((*slot, v.denoted_type(heap)?)))
            .collect();
        let types = values.map_values(|v| v.ty);
        Ok((
            errors,
            ModuleVarTypes {
                types,
                as_types,
                declaration_approximations,
            },
        ))
    })
}
