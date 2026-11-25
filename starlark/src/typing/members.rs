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

//! The attributes the typechecker accepts on a type, for completion.

use crate::typing::Ty;
use crate::typing::TypingOracleCtx;

/// The attributes `x.name` the typechecker accepts for `x: ty`, each with the
/// type it gives `x.name`, sorted by name.
///
/// The list is exactly what the typechecker's attribute check accepts: each
/// candidate name is typed by that check itself, so a listed name and its type
/// cannot drift from it.
///
/// * A union lists the union of its alternatives' members, because the check
///   accepts an attribute any alternative has (so for `T | None`, a listed
///   name may fail at run time on `None`). A name several alternatives have
///   gets the union of their types.
/// * An open type, one that accepts names it cannot list, lists nothing:
///   `Any`, `Never`, callables, `Iter`, `Type`, a value with dynamic
///   attributes, a user type with unknown fields, and any union that has one
///   as an alternative. Structs and namespaces are treated as open too, even
///   one whose fields are all known.
/// * A name that is not an identifier (an enum variant `"my-mode"`) is listed
///   if the check accepts it; the caller decides whether it can be written.
pub fn members(ty: &Ty) -> Vec<(String, Ty)> {
    if ty.is_any() || ty.is_never() {
        return Vec::new();
    }
    let mut names = Vec::new();
    for basic in ty.iter_union() {
        match TypingOracleCtx::expr_dot_names(basic) {
            Some(n) => names.extend(n),
            None => return Vec::new(),
        }
    }
    names.sort_unstable();
    names.dedup();
    names
        .into_iter()
        .filter_map(|name| {
            let member = ty
                .typecheck_union_simple(|basic| TypingOracleCtx::expr_dot_basic(basic, &name))
                .ok()?;
            Some((name, member))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;
    use std::fmt::Write;

    use starlark_syntax::golden_test_template::golden_test_template;

    use crate::codemap::CodeMap;
    use crate::codemap::Span;
    use crate::environment::Globals;
    use crate::environment::Module;
    use crate::eval::Evaluator;
    use crate::syntax::AstModule;
    use crate::syntax::Dialect;
    use crate::typing::Ty;
    use crate::typing::TyStarlarkValue;
    use crate::typing::TyTypedKwargs;
    use crate::typing::TyUser;
    use crate::typing::TyUserFields;
    use crate::typing::TyUserParams;
    use crate::typing::TypingOracleCtx;
    use crate::typing::members;
    use crate::values::Value;
    use crate::values::ValueLike;
    use crate::values::enumeration::EnumType;
    use crate::values::record::Record;
    use crate::values::record::record_type::RecordType;
    use crate::values::typing::TypeInstanceId;

    const DECLARATIONS: &str = r#"
Lib = record(name = str, port = field(int, 80), srcs = field(list[str], []))
Pkg = record(libs = list[Lib], main = Lib)
Mode = enum("debug", "release", "values", "my-mode")
ns = namespace(a = 1)
st = struct(a = 1)
"#;

    struct Declared {
        lib: Ty,
        lib_type: Ty,
        pkg: Ty,
        mode: Ty,
        mode_type: Ty,
        namespace: Ty,
        struct_: Ty,
    }

    fn declared() -> Declared {
        Module::with_temp_heap(|module| {
            let ast =
                AstModule::parse("lib.star", DECLARATIONS.to_owned(), &Dialect::Extended).unwrap();
            let globals = Globals::extended_internal();
            let mut eval = Evaluator::new(&module);
            eval.eval_module(ast, &globals).unwrap();
            drop(eval);

            let record = |name: &str| {
                let value: Value = module.get(name).unwrap();
                let data = value
                    .downcast_ref::<RecordType>()
                    .unwrap()
                    .ty_record_data()
                    .unwrap()
                    .clone();
                (data.ty_record.clone(), data.ty_record_type.clone())
            };
            let (lib, lib_type) = record("Lib");
            let (pkg, _) = record("Pkg");
            let mode_value = module.get("Mode").unwrap();
            let mode_data = mode_value
                .downcast_ref::<EnumType>()
                .unwrap()
                .ty_enum_data()
                .unwrap()
                .clone();
            Declared {
                lib,
                lib_type,
                pkg,
                mode: mode_data.ty_enum_value.clone(),
                mode_type: mode_data.ty_enum_type.clone(),
                namespace: Ty::of_value(module.get("ns").unwrap()),
                struct_: Ty::of_value(module.get("st").unwrap()),
            }
        })
    }

    fn closed_types(d: &Declared) -> Vec<(&'static str, Ty)> {
        vec![
            ("str", Ty::string()),
            ("int", Ty::int()),
            ("bool", Ty::bool()),
            ("tuple", Ty::tuple2(Ty::int(), Ty::string())),
            ("None", Ty::none()),
            ("list[str]", Ty::list(Ty::string())),
            ("dict[str, int]", Ty::dict(Ty::string(), Ty::int())),
            ("set[str]", Ty::set(Ty::string())),
            ("record", d.lib.clone()),
            ("record type", d.lib_type.clone()),
            ("record with a list-of-record field", d.pkg.clone()),
            ("enum type", d.mode_type.clone()),
            ("enum value", d.mode.clone()),
            ("Lib | None", Ty::union2(d.lib.clone(), Ty::none())),
            ("str | None", Ty::union2(Ty::string(), Ty::none())),
            ("Lib | Mode", Ty::union2(d.lib.clone(), d.mode.clone())),
            (
                "typed kwargs",
                TyTypedKwargs::new([("name".to_owned(), Ty::string())]),
            ),
        ]
    }

    fn open_types() -> Vec<(&'static str, Ty)> {
        let unknown_fields = Ty::custom(
            TyUser::new(
                "Provider".to_owned(),
                TyStarlarkValue::new::<Record>(),
                TypeInstanceId::r#gen(),
                TyUserParams {
                    fields: TyUserFields::unknown(),
                    ..TyUserParams::default()
                },
            )
            .unwrap(),
        );
        vec![
            ("Any", Ty::any()),
            // `Never` accepts every attribute (the expression is unreachable).
            ("Never", Ty::never()),
            ("Callable", Ty::any_callable()),
            ("Iter", Ty::iter(Ty::string())),
            ("Type", Ty::basic(crate::typing::TyBasic::Type)),
            ("struct type", Ty::any_struct()),
            ("user type with unknown fields", unknown_fields.clone()),
            ("open | str", Ty::union2(unknown_fields, Ty::string())),
        ]
    }

    fn accepts(ty: &Ty, name: &str) -> Option<Ty> {
        let codemap = CodeMap::default();
        let ctx = TypingOracleCtx { codemap: &codemap };
        ctx.expr_dot(Span::default(), ty, name).ok()
    }

    /// I7: for a closed type, `members` is exactly the set of names the
    /// checker accepts, over a vocabulary of every type's members plus names
    /// no type has, each with the type the checker gives it.
    #[test]
    fn members_agree_with_expr_dot() {
        let d = declared();
        let closed = closed_types(&d);

        let mut vocabulary: BTreeSet<String> = closed
            .iter()
            .flat_map(|(_, ty)| members(ty).into_iter().map(|(n, _)| n))
            .collect();
        for bogus in ["nope", "Lib", "Mode", "", "name ", "__dict__", "items2"] {
            vocabulary.insert(bogus.to_owned());
        }

        for (label, ty) in &closed {
            let listed = members(ty);
            let listed_names: BTreeSet<String> = listed.iter().map(|(n, _)| n.clone()).collect();
            assert_eq!(
                listed.len(),
                listed_names.len(),
                "{label}: a name is listed twice"
            );
            let accepted: BTreeSet<String> = vocabulary
                .iter()
                .filter(|n| accepts(ty, n).is_some())
                .cloned()
                .collect();
            assert_eq!(listed_names, accepted, "{label} (`{ty}`)");
            for (name, member) in &listed {
                assert_eq!(
                    Some(member),
                    accepts(ty, name).as_ref(),
                    "{label}: type of `.{name}`"
                );
            }
        }

        for (label, ty) in open_types() {
            assert_eq!(members(&ty), Vec::new(), "{label} (`{ty}`) is open");
            assert!(
                accepts(&ty, "nope").is_some(),
                "{label} (`{ty}`) accepts names it cannot list"
            );
        }

        // I7 lists structs and namespaces as open, so even one whose fields
        // are all known (and which the checker closes) lists nothing.
        for (label, ty) in [("namespace", d.namespace), ("struct", d.struct_)] {
            assert_eq!(members(&ty), Vec::new(), "{label} (`{ty}`) lists nothing");
            assert!(accepts(&ty, "a").is_some(), "{label} (`{ty}`) has `a`");
        }
    }

    /// The shape of the closed types' lists, as specific names.
    #[test]
    fn members_of_declared_types() {
        let d = declared();
        let names = |ty: &Ty| -> Vec<String> { members(ty).into_iter().map(|(n, _)| n).collect() };

        assert_eq!(names(&d.lib), ["name", "port", "srcs"]);
        assert_eq!(names(&d.pkg), ["libs", "main"]);
        assert_eq!(
            names(&Ty::tuple2(Ty::int(), Ty::int())),
            Vec::<String>::new()
        );
        assert_eq!(names(&Ty::none()), Vec::<String>::new());
        // D3: variants, including one that is not an identifier and one that
        // collides with a method (listed once, as the method).
        let mode_type = names(&d.mode_type);
        for variant in ["debug", "release", "my-mode", "values"] {
            assert!(mode_type.iter().any(|n| n == variant), "{variant}");
        }
        assert_eq!(names(&d.mode), ["index", "value"]);
        assert_eq!(
            names(&Ty::union2(d.lib.clone(), Ty::none())),
            ["name", "port", "srcs"]
        );
        let kwargs = names(&TyTypedKwargs::new([("name".to_owned(), Ty::string())]));
        assert_eq!(kwargs, names(&Ty::dict(Ty::string(), Ty::string())));
    }

    /// D7: a member's type as the typechecker prints it.
    #[test]
    fn members_display() {
        let d = declared();
        let mut out = String::new();
        for (label, ty) in [
            ("Lib", d.lib.clone()),
            ("record[Lib]", d.lib_type.clone()),
            ("Pkg", d.pkg.clone()),
            ("enum[Mode]", d.mode_type.clone()),
            ("Mode", d.mode.clone()),
            ("Lib | None", Ty::union2(d.lib.clone(), Ty::none())),
            ("Lib | Mode", Ty::union2(d.lib.clone(), d.mode.clone())),
            ("list[str]", Ty::list(Ty::string())),
            (
                "typed_kwargs",
                TyTypedKwargs::new([("name".to_owned(), Ty::string())]),
            ),
        ] {
            writeln!(out, "{label}:").unwrap();
            for (name, member) in members(&ty) {
                writeln!(out, "  {name}: {member}").unwrap();
            }
        }
        golden_test_template("src/typing/tests/golden/members_display.golden", &out);
    }
}
