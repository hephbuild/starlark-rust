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

//! Typed kwargs: a per-key type for `**kwargs`, like Python's
//! `**kwargs: Unpack[TypedDict]` with every key optional.
//!
//! `def f(name, **kwargs: K)`, where `K` is a [`TyTypedKwargs`], means:
//!
//! * to the typechecker (both modes), `f` takes one optional named-only
//!   parameter per key of `K` and no `**` catch-all, so a caller's keyword
//!   argument is checked against its key's type, and an unknown key is an
//!   error. [`ParamSpec::new_parts`](crate::typing::ParamSpec::new_parts) does
//!   the expansion. A key named like an explicit parameter of `f` is dropped:
//!   that parameter binds the argument, so `kwargs` never holds it.
//! * inside the body, `kwargs` is a `dict[str, <union of the key types>]`.
//! * at runtime, the `kwargs` dict must hold only known keys, each value
//!   matching its key's type; the error names the key.

use std::fmt;
use std::fmt::Display;
use std::fmt::Formatter;

use allocative::Allocative;
use dupe::Dupe;
use pagable::Pagable;
use pagable::pagable_typetag;
use starlark_derive::type_matcher;
use starlark_map::sorted_map::SortedMap;

use crate as starlark;
use crate::typing::Ty;
use crate::typing::TyBasic;
use crate::typing::custom::TyCustomDyn;
use crate::typing::custom::TyCustomImpl;
use crate::typing::error::TypingNoContextError;
use crate::typing::error::TypingNoContextOrInternalError;
use crate::typing::oracle::ctx::TypingOracleCtx;
use crate::util::arc_str::ArcStr;
use crate::values::Value;
use crate::values::dict::DictRef;
use crate::values::typing::type_compiled::alloc::TypeMatcherAlloc;
use crate::values::typing::type_compiled::matcher::TypeMatcher;
use crate::values::typing::type_compiled::matcher::TypeMatcherBox;
use crate::values::typing::type_compiled::matcher::TypeMatcherBoxAlloc;
use crate::values::typing::type_compiled::matcher::TypeMatcherDyn;

/// The type of a `**kwargs` parameter with a closed set of keys, each with
/// its own type, every key optional.
///
/// Construct it with [`TyTypedKwargs::new`], and expose it to Starlark as a
/// value whose `StarlarkValue::eval_type` returns that [`Ty`], so it can be
/// written as the annotation of `**kwargs`. Anywhere else (a regular
/// parameter, a variable) it is the type of a dict with those keys.
#[derive(
    Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Allocative, Pagable
)]
#[pagable_typetag(TyCustomDyn)]
pub struct TyTypedKwargs {
    fields: SortedMap<ArcStr, Ty>,
}

impl TyTypedKwargs {
    /// Typed kwargs with these keys and types. A key given twice takes the
    /// later type.
    pub fn new(fields: impl IntoIterator<Item = (String, Ty)>) -> Ty {
        Ty::custom(TyTypedKwargs {
            fields: fields
                .into_iter()
                .map(|(k, v)| (ArcStr::from(k.as_str()), v))
                .collect(),
        })
    }

    /// `ty` as typed kwargs, if it is exactly one.
    pub fn from_ty(ty: &Ty) -> Option<&TyTypedKwargs> {
        match ty.iter_union() {
            [TyBasic::Custom(c)] => c.0.as_any().downcast_ref::<TyTypedKwargs>(),
            _ => None,
        }
    }

    /// The keys and their types, sorted by key.
    pub fn fields(&self) -> impl ExactSizeIterator<Item = (&str, &Ty)> {
        self.fields.iter().map(|(k, v)| (k.as_str(), v))
    }

    pub(crate) fn fields_arc(&self) -> impl ExactSizeIterator<Item = (&ArcStr, &Ty)> {
        self.fields.iter()
    }

    /// The type of any one value: the union of the key types.
    pub(crate) fn value_ty(&self) -> Ty {
        Ty::unions(self.fields.values().cloned().collect())
    }

    /// Why `value` is not a dict of this type, naming the offending key; `None`
    /// if it is not a dict at all (or matches), and the generic message applies.
    pub(crate) fn mismatch(&self, value: Value, arg_name: &str) -> Option<String> {
        let dict = DictRef::from_value(value)?;
        for (k, v) in dict.iter() {
            let Some(key) = k.unpack_str() else {
                return Some(format!(
                    "Key `{}` of type `{}` is not a string, for argument `{arg_name}`",
                    k.to_repr(),
                    k.get_type()
                ));
            };
            let Some(ty) = self.fields.get(key) else {
                let known: Vec<String> = self.fields.keys().map(|k| format!("`{k}`")).collect();
                return Some(format!(
                    "Unexpected key `{key}` for argument `{arg_name}`; known keys: {}",
                    known.join(", ")
                ));
            };
            if !TypeMatcherBoxAlloc.ty(ty).matches(v) {
                return Some(format!(
                    "Value `{}` of type `{}` for key `{key}` does not match the type annotation `{ty}` for argument `{arg_name}`",
                    v.to_str(),
                    v.get_type()
                ));
            }
        }
        None
    }
}

impl TyCustomImpl for TyTypedKwargs {
    fn as_name(&self) -> Option<&str> {
        Some("dict")
    }

    fn iter_item(&self) -> Result<Ty, TypingNoContextError> {
        Ok(Ty::string())
    }

    fn index(
        &self,
        _item: &TyBasic,
        _ctx: &TypingOracleCtx,
    ) -> Result<Ty, TypingNoContextOrInternalError> {
        Ok(self.value_ty())
    }

    fn attribute(&self, _attr: &str) -> Result<Ty, TypingNoContextError> {
        // A dict's methods. Lenient rather than wrong: the typechecker must
        // not refuse what evaluation accepts.
        Ok(Ty::any())
    }

    fn intersects_with(&self, other: &TyBasic) -> bool {
        matches!(other, TyBasic::Dict(..)) || other.as_name() == Some("dict")
    }

    fn matcher<T: TypeMatcherAlloc>(&self, factory: T) -> T::Result {
        let mut fields: Vec<(ArcStr, TypeMatcherBox)> = self
            .fields
            .iter()
            .map(|(k, ty)| (k.dupe(), TypeMatcherBoxAlloc.ty(ty)))
            .collect();
        // The matcher binary-searches by `str` order.
        fields.sort_by(|(a, _), (b, _)| a.as_str().cmp(b.as_str()));
        factory.alloc(IsTypedKwargs(fields))
    }
}

impl Display for TyTypedKwargs {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        display_container::fmt_container(
            f,
            "typed_kwargs(",
            ")",
            self.fields.iter().map(|(k, v)| format!("{k} = {v}")),
        )
    }
}

/// Matches a dict whose keys are all known strings, each value matching its
/// key's type. Sorted by key.
#[derive(Clone, Allocative, Debug, Pagable)]
#[pagable_typetag(TypeMatcherDyn)]
struct IsTypedKwargs(Vec<(ArcStr, TypeMatcherBox)>);

#[type_matcher]
impl TypeMatcher for IsTypedKwargs {
    fn matches(&self, value: Value) -> bool {
        let Some(dict) = DictRef::from_value(value) else {
            return false;
        };
        dict.iter().all(|(k, v)| {
            let Some(k) = k.unpack_str() else {
                return false;
            };
            match self.0.binary_search_by(|(key, _)| key.as_str().cmp(k)) {
                Ok(i) => self.0[i].1.matches(v),
                Err(_) => false,
            }
        })
    }
}
