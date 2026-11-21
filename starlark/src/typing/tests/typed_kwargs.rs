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

//! `**kwargs: <typed kwargs>`: a per-key type for `**kwargs`.

use std::fmt::Write;

use allocative::Allocative;
use starlark_derive::NoSerialize;
use starlark_derive::ProvidesStaticType;
use starlark_derive::starlark_value;
use starlark_syntax::golden_test_template::golden_test_template;

use crate as starlark;
use crate::environment::GlobalsBuilder;
use crate::environment::Module;
use crate::eval::Evaluator;
use crate::syntax::AstModule;
use crate::syntax::Dialect;
use crate::tests::util::trim_rust_backtrace;
use crate::typing::Ty;
use crate::typing::TyTypedKwargs;
use crate::typing::tests::TypeCheck;
use crate::typing::tests::typecheck_globals;
use crate::values::StarlarkValue;

/// A type value behind an attribute path, the way an embedder exposes one
/// (`ns.bash.Kwargs`): a value whose `eval_type()` is the typed kwargs.
#[derive(
    Debug,
    derive_more::Display,
    ProvidesStaticType,
    NoSerialize,
    Allocative
)]
#[display("ns.bash.Kwargs")]
struct KwargsAlias(Ty);

crate::starlark_simple_value!(KwargsAlias);

#[starlark_value(type = "type")]
impl<'v> StarlarkValue<'v> for KwargsAlias {
    fn eval_type(&self) -> Option<Ty> {
        Some(self.0.clone())
    }
}

/// `ns.bash.Kwargs`: `name` (shadowed by the defs' own `name` parameter),
/// `run`, `count` and `deps`.
pub(super) fn register_typed_kwargs_globals(globals: &mut GlobalsBuilder) {
    globals.namespace("ns", |ns| {
        ns.namespace("bash", |bash| {
            bash.set(
                "Kwargs",
                KwargsAlias(TyTypedKwargs::new([
                    ("name".to_owned(), Ty::string()),
                    ("run".to_owned(), Ty::string()),
                    ("count".to_owned(), Ty::int()),
                    (
                        "deps".to_owned(),
                        Ty::union2(Ty::list(Ty::string()), Ty::none()),
                    ),
                ])),
            )
        })
    });
}

#[test]
fn test_typed_kwargs_known_key_ok() {
    TypeCheck::new().ty("kw").check(
        "typed_kwargs_known_key_ok",
        r#"
def f(name: str, **kwargs: ns.bash.Kwargs):
    kw = kwargs

def g():
    f(name = "a")
    f(name = "a", run = "echo")
    f(name = "a", run = "echo", count = 1, deps = ["x"])
    f(name = "a", deps = None)
"#,
    );
}

#[test]
fn test_typed_kwargs_wrong_type() {
    TypeCheck::new().check(
        "typed_kwargs_wrong_type",
        r#"
def f(name: str, **kwargs: ns.bash.Kwargs):
    pass

def g():
    f(name = "a", run = 1)
"#,
    );
}

#[test]
fn test_typed_kwargs_unknown_key() {
    TypeCheck::new().check(
        "typed_kwargs_unknown_key",
        r#"
def f(name: str, **kwargs: ns.bash.Kwargs):
    pass

def g():
    f(name = "a", rnu = "echo")
"#,
    );
}

/// A def's type reaches a loading module through its `Interface`.
#[test]
fn test_typed_kwargs_across_load() {
    let (interface, module) = TypeCheck::new().check(
        "typed_kwargs_across_load_0",
        r#"
def lib(name: str, **kwargs: ns.bash.Kwargs):
    pass
"#,
    );
    TypeCheck::new().load("lib.bzl", interface, module).check(
        "typed_kwargs_across_load_1",
        r#"
load("lib.bzl", "lib")

def g():
    lib(name = "a", run = "echo")
    lib(name = "a", rnu = "echo")
"#,
    );
}

#[test]
fn test_typed_kwargs_forwarding() {
    TypeCheck::new().check(
        "typed_kwargs_forwarding",
        r#"
def target(name: str, run: str = "", count: int = 0, deps: list[str] | None = None):
    pass

def f(name: str, **kwargs: ns.bash.Kwargs):
    target(name = name, **kwargs)

def f2(name: str, **kwargs: ns.bash.Kwargs):
    f(name = name, **kwargs)

def g():
    f2(name = "a", run = "echo", count = 1)

g()
"#,
    );
}

#[test]
fn test_plain_kwargs_unchanged() {
    TypeCheck::new().ty("kw").check(
        "plain_kwargs_unchanged",
        r#"
def f(**kwargs: int):
    kw = kwargs

def g():
    f(a = 1)
    f(b = "x")
"#,
    );
}

/// Evaluation alone (no static typechecking) rejects an unknown key and a
/// value of the wrong type, naming the key.
#[test]
fn test_typed_kwargs_eval() {
    const DEF: &str = r#"
def f(name: str, **kwargs: ns.bash.Kwargs):
    return kwargs
"#;
    let globals = typecheck_globals();
    let mut output = String::new();
    for call in [
        r#"f(name = "a", run = "echo", count = 1, deps = None)"#,
        r#"f(name = "a", rnu = "echo")"#,
        r#"f(name = "a", run = 1)"#,
        r#"f(name = "a", deps = [1])"#,
    ] {
        let code = format!("{}\n{call}\n", DEF.trim());
        writeln!(output, "Code:\n{call}\n").unwrap();
        let ast = AstModule::parse("filename", code, &Dialect::AllOptionsInternal).unwrap();
        Module::with_temp_heap(|module| {
            let mut eval = Evaluator::new(&module);
            match eval.eval_module(ast, &globals) {
                Ok(_) => writeln!(output, "No errors.\n").unwrap(),
                Err(e) => writeln!(output, "{}\n", trim_rust_backtrace(&format!("{e:?}"))).unwrap(),
            }
            crate::Result::Ok(())
        })
        .unwrap();
    }
    golden_test_template(
        "src/typing/tests/golden/typed_kwargs_eval.golden",
        output.trim_end(),
    );
}
