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

//! `error_types` and `Ty::user_type_ids`: which declared types an error is
//! about, by identity rather than by text.

use std::collections::HashMap;
use std::collections::HashSet;

use dupe::Dupe;

use crate::codemap::CodeMap;
use crate::codemap::Span;
use crate::environment::Globals;
use crate::environment::Module;
use crate::eval::Evaluator;
use crate::syntax::AstModule;
use crate::syntax::Dialect;
use crate::typing::AstModuleTypecheck;
use crate::typing::ParamSpec;
use crate::typing::Ty;
use crate::typing::TyTypedKwargs;
use crate::typing::TypingBinOp;
use crate::typing::TypingOracleCtx;
use crate::typing::TypingUnOp;
use crate::typing::error::TypingError;
use crate::typing::error_types;
use crate::typing::oracle::ctx::TypingOracleCtxError;
use crate::values::Value;
use crate::values::ValueLike;
use crate::values::enumeration::EnumType;
use crate::values::record::record_type::RecordType;
use crate::values::typing::TypeInstanceId;

struct Declared {
    lib: Ty,
    lib_type: Ty,
    pkg: Ty,
    mode: Ty,
    mode_type: Ty,
}

fn declared() -> Declared {
    Module::with_temp_heap(|module| {
        let code = r#"
Lib = record(name = str)
Pkg = record(libs = list[Lib])
Mode = enum("debug", "release")
"#;
        let ast = AstModule::parse("lib.star", code.to_owned(), &Dialect::Extended).unwrap();
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
                .dupe();
            (data.ty_record.dupe(), data.ty_record_type.dupe())
        };
        let (lib, lib_type) = record("Lib");
        let (pkg, _) = record("Pkg");
        let mode = module.get("Mode").unwrap();
        let mode = mode
            .downcast_ref::<EnumType>()
            .unwrap()
            .ty_enum_data()
            .unwrap()
            .dupe();
        Declared {
            lib,
            lib_type,
            pkg,
            mode: mode.ty_enum_value.dupe(),
            mode_type: mode.ty_enum_type.dupe(),
        }
    })
}

/// Every variant of `TypingOracleCtxError`. A new variant does not compile in
/// `kind` until it is named here and given a row in `rows`.
const KINDS: &[&str] = &[
    "IncompatibleType",
    "CallToNonCallable",
    "MissingRequiredParameter",
    "UnexpectedNamedArgument",
    "TooManyPositionalArguments",
    "CallArgumentsIncompatible",
    "MissingIndexOperator",
    "MissingSliceOperator",
    "AttributeNotAvailable",
    "NotIterable",
    "UnaryOperatorNotAvailable",
    "BinaryOperatorNotAvailable",
];

fn kind(e: &TypingOracleCtxError) -> &'static str {
    // No wildcard: a new variant fails to compile here.
    match e {
        TypingOracleCtxError::IncompatibleType { .. } => "IncompatibleType",
        TypingOracleCtxError::CallToNonCallable { .. } => "CallToNonCallable",
        TypingOracleCtxError::MissingRequiredParameter { .. } => "MissingRequiredParameter",
        TypingOracleCtxError::UnexpectedNamedArgument { .. } => "UnexpectedNamedArgument",
        TypingOracleCtxError::TooManyPositionalArguments => "TooManyPositionalArguments",
        TypingOracleCtxError::CallArgumentsIncompatible { .. } => "CallArgumentsIncompatible",
        TypingOracleCtxError::MissingIndexOperator { .. } => "MissingIndexOperator",
        TypingOracleCtxError::MissingSliceOperator { .. } => "MissingSliceOperator",
        TypingOracleCtxError::AttributeNotAvailable { .. } => "AttributeNotAvailable",
        TypingOracleCtxError::NotIterable { .. } => "NotIterable",
        TypingOracleCtxError::UnaryOperatorNotAvailable { .. } => "UnaryOperatorNotAvailable",
        TypingOracleCtxError::BinaryOperatorNotAvailable { .. } => "BinaryOperatorNotAvailable",
    }
}

/// One row per kind: the error, the types its message mentions in order, and
/// the backticked words in the message that are not types. Names that spell
/// a declared type (`Lib`, `Mode`) are used as attribute and parameter names
/// on purpose.
fn rows(d: &Declared) -> Vec<(TypingOracleCtxError, Vec<Ty>, &'static [&'static str])> {
    let fun = Ty::function(ParamSpec::pos_only([d.lib.dupe()], []), d.mode.dupe());
    let lib_list = Ty::list(d.lib.dupe());
    vec![
        (
            TypingOracleCtxError::IncompatibleType {
                got: Ty::int(),
                require: lib_list.dupe(),
            },
            vec![lib_list.dupe(), Ty::int()],
            &[],
        ),
        (
            TypingOracleCtxError::CallToNonCallable {
                ty: lib_list.dupe(),
            },
            vec![lib_list.dupe()],
            &[],
        ),
        (
            TypingOracleCtxError::MissingRequiredParameter {
                name: "Lib".to_owned(),
            },
            vec![],
            &["Lib"],
        ),
        (
            TypingOracleCtxError::UnexpectedNamedArgument {
                name: "Mode".to_owned(),
            },
            vec![],
            &["Mode"],
        ),
        (
            TypingOracleCtxError::TooManyPositionalArguments,
            vec![],
            &[],
        ),
        (
            TypingOracleCtxError::CallArgumentsIncompatible { fun: fun.dupe() },
            vec![fun.dupe()],
            &[],
        ),
        (
            TypingOracleCtxError::MissingIndexOperator {
                ty: d.mode.dupe(),
                index: d.lib.dupe(),
            },
            vec![d.mode.dupe(), d.lib.dupe()],
            &[],
        ),
        (
            TypingOracleCtxError::MissingSliceOperator {
                ty: d.lib_type.dupe(),
            },
            vec![d.lib_type.dupe()],
            &[],
        ),
        (
            TypingOracleCtxError::AttributeNotAvailable {
                ty: d.lib.dupe(),
                attr: "Mode".to_owned(),
            },
            vec![d.lib.dupe()],
            &["Mode"],
        ),
        (
            TypingOracleCtxError::NotIterable { ty: d.pkg.dupe() },
            vec![d.pkg.dupe()],
            &[],
        ),
        (
            TypingOracleCtxError::UnaryOperatorNotAvailable {
                ty: d.mode.dupe(),
                un_op: TypingUnOp::Minus,
            },
            vec![d.mode.dupe()],
            &["-"],
        ),
        (
            TypingOracleCtxError::BinaryOperatorNotAvailable {
                bin_op: TypingBinOp::Add,
                left: Ty::union2(d.lib.dupe(), Ty::none()),
                right: Ty::dict(Ty::string(), d.mode.dupe()),
            },
            vec![
                Ty::union2(d.lib.dupe(), Ty::none()),
                Ty::dict(Ty::string(), d.mode.dupe()),
            ],
            &["+"],
        ),
    ]
}

/// The backticked words of a message, in order.
fn backticked(message: &str) -> Vec<&str> {
    message.split('`').skip(1).step_by(2).collect()
}

/// D2.7: every kind of typechecker error reports the types its message
/// mentions, in message order, through `into_error`; nothing else in the
/// message counts as a type.
#[test]
fn error_types_cover_every_kind() {
    let d = declared();
    let codemap = CodeMap::default();
    let ctx = TypingOracleCtx { codemap: &codemap };

    let rows = rows(&d);
    let covered: HashSet<&str> = rows.iter().map(|(e, _, _)| kind(e)).collect();
    let all: HashSet<&str> = KINDS.iter().copied().collect();
    assert_eq!(covered, all, "every kind has a row");
    assert_eq!(rows.len(), KINDS.len(), "one row per kind");

    for (error, types, non_types) in rows {
        let label = kind(&error);
        let message = error.to_string();

        // The row agrees with the message: each backticked word is the next
        // type, or a declared non-type word.
        let mut expected = types.iter().peekable();
        for word in backticked(&message) {
            if expected.peek().is_some_and(|t| t.to_string() == word) {
                expected.next();
            } else {
                assert!(
                    non_types.contains(&word),
                    "{label}: `{word}` in {message:?} is neither the next type nor a known word"
                );
            }
        }
        assert!(
            expected.next().is_none(),
            "{label}: {message:?} does not mention every type in its row"
        );

        let error = ctx.mk_error(Span::default(), error).into_error();
        assert_eq!(
            error.to_string().lines().next(),
            Some(format!("error: {message}").as_str())
        );
        assert_eq!(error_types(&error), types, "{label}: {message}");
    }
}

/// An error built from a plain message mentions no type, even one whose
/// text spells a type.
#[test]
fn error_types_of_a_plain_message_is_empty() {
    let codemap = CodeMap::default();
    let error = TypingError::msg(
        "Expected type `Lib` but got `int`",
        Span::default(),
        &codemap,
    )
    .into_error();
    assert_eq!(error_types(&error), Vec::new());
    let error = crate::Error::new_other(anyhow::anyhow!("Type `Lib` is not iterable"));
    assert_eq!(error_types(&error), Vec::new());
}

/// From a real typecheck run: the errors it returns keep their types.
#[test]
fn error_types_from_typecheck() {
    let code = r#"
Lib = record(name = str)
Mode = enum("debug", "release")

def want_mode(m: Mode):
    pass

def bad(l: Lib):
    want_mode("debug")
    l.Mode
"#;
    let ast = AstModule::parse("lib.star", code.to_owned(), &Dialect::Extended).unwrap();
    let (errors, ..) = ast.typecheck(&Globals::extended_internal(), &HashMap::new());
    let found: Vec<(String, Vec<String>)> = errors
        .iter()
        .map(|e| {
            (
                e.to_string().lines().next().unwrap().to_owned(),
                error_types(e).iter().map(|t| t.to_string()).collect(),
            )
        })
        .collect();
    assert_eq!(
        found,
        [
            (
                "error: Expected type `Mode` but got `str`".to_owned(),
                vec!["Mode".to_owned(), "str".to_owned()]
            ),
            (
                "error: The attribute `Mode` is not available on the type `Lib`".to_owned(),
                vec!["Lib".to_owned()]
            ),
        ]
    );
    for e in &errors {
        let types = error_types(e);
        assert_eq!(types[0].user_type_ids().len(), 1, "{e}");
    }
}

fn id(ty: &Ty) -> TypeInstanceId {
    match ty.user_type_ids().as_slice() {
        [id] => *id,
        ids => panic!("`{ty}` is one user type, got {ids:?}"),
    }
}

/// `user_type_ids` walks what a type prints, not a user type's fields.
#[test]
fn user_type_ids_walk_what_is_printed() {
    let d = declared();
    let lib = id(&d.lib);
    let mode = id(&d.mode);
    let pkg = id(&d.pkg);
    assert_ne!(lib, mode);

    let cases: Vec<(&str, Ty, Vec<TypeInstanceId>)> = vec![
        ("str", Ty::string(), vec![]),
        ("list[Lib]", Ty::list(d.lib.dupe()), vec![lib]),
        (
            "Lib | None",
            Ty::union2(d.lib.dupe(), Ty::none()),
            vec![lib],
        ),
        (
            "dict[str, Mode]",
            Ty::dict(Ty::string(), d.mode.dupe()),
            vec![mode],
        ),
        (
            "dict[Mode, list[Lib]]",
            Ty::dict(d.mode.dupe(), Ty::list(d.lib.dupe())),
            vec![mode, lib],
        ),
        (
            "tuple[Lib, Mode, Lib]",
            Ty::tuple(vec![d.lib.dupe(), d.mode.dupe(), d.lib.dupe()]),
            vec![lib, mode],
        ),
        ("set[Mode]", Ty::set(d.mode.dupe()), vec![mode]),
        ("Iter[Lib]", Ty::iter(d.lib.dupe()), vec![lib]),
        (
            "def(Lib) -> Mode",
            Ty::function(ParamSpec::pos_only([d.lib.dupe()], []), d.mode.dupe()),
            vec![lib, mode],
        ),
        (
            "typed_kwargs(a = Mode)",
            TyTypedKwargs::new([("a".to_owned(), d.mode.dupe())]),
            vec![mode],
        ),
        // `Pkg` prints as its name: its `libs: list[Lib]` field is not named.
        ("Pkg", d.pkg.dupe(), vec![pkg]),
    ];
    for (label, ty, ids) in cases {
        assert_eq!(ty.user_type_ids(), ids, "{label} (`{ty}`)");
    }

    // A type's own type names the type it constructs.
    let lib_type = d.lib_type.user_type_ids();
    assert_eq!(lib_type.len(), 2, "record[Lib]: {lib_type:?}");
    assert_eq!(lib_type[1], lib);
    let mode_type = d.mode_type.user_type_ids();
    assert_eq!(mode_type.len(), 2, "enum[Mode]: {mode_type:?}");
    assert_eq!(mode_type[1], mode);
}
