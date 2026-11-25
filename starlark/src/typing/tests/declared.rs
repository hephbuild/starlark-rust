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

//! Record and enum types declared by the module itself: `record(...)`,
//! `field(...)` and `enum(...)`.

use std::collections::HashMap;
use std::fmt::Write;

use starlark_map::small_map::SmallMap;
use starlark_syntax::golden_test_template::golden_test_template;

use crate::environment::Globals;
use crate::environment::Module;
use crate::eval::Evaluator;
use crate::syntax::AstModule;
use crate::syntax::Dialect;
use crate::typing::AstModuleTypecheck;
use crate::typing::Ty;
use crate::typing::interface::Interface;
use crate::values::Heap;
use crate::values::Value;
use crate::values::ValueLike;
use crate::values::enumeration::EnumType;
use crate::values::list::AllocList;
use crate::values::record::field::FieldGen;
use crate::values::record::record_type::RecordType;
use crate::values::typing::type_compiled::compiled::TypeCompiled;

/// A `Ty` as text: its display, then its debug form with every
/// `TypeInstanceId` renumbered by first appearance in `out`, so the text is
/// stable across runs and still shows which ids are the same.
fn describe(out: &mut String, label: &str, ty: &Ty) {
    writeln!(out, "{label}: {ty}").unwrap();
    writeln!(out, "{ty:#?}").unwrap();
}

fn renumber_ids(text: &str) -> String {
    let re = regex::Regex::new(r"TypeInstanceId\(\s*(\d+),?\s*\)").unwrap();
    let mut seen: HashMap<String, usize> = HashMap::new();
    re.replace_all(text, |c: &regex::Captures| {
        let n = seen.len();
        let k = *seen.entry(c[1].to_owned()).or_insert(n);
        format!("TypeInstanceId(#{k})")
    })
    .into_owned()
}

fn describe_record(out: &mut String, name: &str, value: Value) {
    let record = value
        .downcast_ref::<RecordType>()
        .unwrap_or_else(|| panic!("`{name}` is a record type"));
    let data = record.ty_record_data().expect("named");
    writeln!(out, "{name}.name: {}", data.name).unwrap();
    describe(out, &format!("{name} instance"), &data.ty_record);
    describe(out, &format!("{name} type"), &data.ty_record_type);
}

/// A second name bound to a record type: the first name sticks.
fn describe_alias(out: &mut String, name: &str, value: Value) {
    let record = value
        .downcast_ref::<RecordType>()
        .unwrap_or_else(|| panic!("`{name}` is a record type"));
    let data = record.ty_record_data().expect("named");
    writeln!(
        out,
        "{name}.name: {}, instance: {}, type: {}",
        data.name, data.ty_record, data.ty_record_type
    )
    .unwrap();
}

fn describe_enum(out: &mut String, name: &str, value: Value) {
    let enum_type = value
        .downcast_ref::<EnumType>()
        .unwrap_or_else(|| panic!("`{name}` is an enum type"));
    let data = enum_type.ty_enum_data().expect("named");
    writeln!(out, "{name}.name: {}", data.name).unwrap();
    describe(out, &format!("{name} value"), &data.ty_enum_value);
    describe(out, &format!("{name} type"), &data.ty_enum_type);
}

const DECLARATIONS: &str = r#"
Lib = record(
    name = str,
    port = field(int, 80),
    srcs = field(list[str], []),
    opt = field(str | None, None),
)
Lib2 = Lib
Mode = enum("debug", "release")
"#;

/// The types `export_as` gives a record and an enum, pinned by a golden, and
/// `init_ty` giving the same types to the same declaration built in Rust.
#[test]
fn export_as_unchanged() {
    let evaluated = Module::with_temp_heap(|module| {
        let ast =
            AstModule::parse("lib.star", DECLARATIONS.to_owned(), &Dialect::Extended).unwrap();
        let globals = Globals::extended_internal();
        let mut eval = Evaluator::new(&module);
        eval.eval_module(ast, &globals).unwrap();
        drop(eval);

        let mut out = String::new();
        describe_record(&mut out, "Lib", module.get("Lib").unwrap());
        describe_alias(&mut out, "Lib2", module.get("Lib2").unwrap());
        describe_enum(&mut out, "Mode", module.get("Mode").unwrap());
        renumber_ids(&out)
    });

    golden_test_template(
        "src/typing/tests/golden/export_as_unchanged.golden",
        &evaluated,
    );

    let built = Heap::temp(|heap| {
        let none = Value::new_none();
        let mut fields = SmallMap::new();
        fn field<'v>(heap: Heap<'v>, ty: Ty, default: Option<Value<'v>>) -> FieldGen<Value<'v>> {
            FieldGen::new(TypeCompiled::from_ty(&ty, heap), default)
        }
        fields.insert("name".to_owned(), field(heap, Ty::string(), None));
        fields.insert(
            "port".to_owned(),
            field(heap, Ty::int(), Some(heap.alloc(80))),
        );
        fields.insert(
            "srcs".to_owned(),
            field(
                heap,
                Ty::list(Ty::string()),
                Some(heap.alloc(AllocList::EMPTY)),
            ),
        );
        fields.insert(
            "opt".to_owned(),
            field(heap, Ty::union2(Ty::string(), Ty::none()), Some(none)),
        );
        let record = heap.alloc(RecordType::new(fields));
        record
            .downcast_ref::<RecordType>()
            .unwrap()
            .init_ty("Lib")
            .unwrap();
        record
            .downcast_ref::<RecordType>()
            .unwrap()
            .init_ty("Lib2")
            .unwrap();

        let mode = EnumType::new(
            vec![heap.alloc_str("debug"), heap.alloc_str("release")],
            heap,
        )
        .unwrap();
        mode.init_ty("Mode").unwrap();

        let mut out = String::new();
        describe_record(&mut out, "Lib", record);
        describe_alias(&mut out, "Lib2", record);
        describe_enum(&mut out, "Mode", mode.to_value());
        renumber_ids(&out)
    });

    assert_eq!(evaluated, built);
}

#[test]
fn declared_record_and_enum_checked() {
    crate::typing::tests::TypeCheck::new().check(
        "declared_record_and_enum_checked",
        r#"
F = field(str)
Lib = record(name = str, port = field(int, 80), srcs = field(list[str], []), alias = F)
Mode = enum("debug", "release")
Libs = list[Lib]
Opt = Lib | None

def ok(l: Lib, m: Mode, ls: Libs, o: Opt) -> str:
    l.srcs.append("x")
    return l.name + m.value + ls[0].name

def bad_field(l: Lib):
    l.nme

def bad_arg():
    Lib(name = 1, alias = "a")

def bad_enum(m: Mode):
    pass

def call_bad_enum():
    bad_enum("debug")
"#,
    );
}

#[test]
fn declarations_approximated_as_any() {
    crate::typing::tests::TypeCheck::new().check(
        "declarations_approximated_as_any",
        r#"
Twice = record(a = str)
Twice = record(a = int)
if len([]) > 0:
    Cond = record(a = str)
Mode = enum("a", "a")
Star = record(**{"a": str})
NonLit = enum("a" + "b")

def f(t: Twice, c: Cond, m: Mode, s: Star, n: NonLit):
    Local = record(a = str)
    t.nope
    c.nope
    m.nope
    s.nope
    n.nope
"#,
    );
}

/// Typecheck `code` against `loads` without evaluating it; the errors as
/// text and the interface.
fn typecheck_only(code: &str, loads: &[(&str, &Interface)]) -> (Vec<String>, Interface) {
    let ast = AstModule::parse("filename", code.to_owned(), &Dialect::AllOptionsInternal).unwrap();
    let loads = loads
        .iter()
        .map(|(name, interface)| ((*name).to_owned(), (*interface).clone()))
        .collect();
    let (errors, _typemap, interface, _approximations) =
        ast.typecheck(&super::typecheck_globals(), &loads);
    (errors.iter().map(|e| format!("{e:#}")).collect(), interface)
}

/// `name: type` for each of `names`, as the interface has them.
fn interface_types(interface: &Interface, names: &[&str]) -> String {
    let mut out = String::new();
    for name in names {
        match interface.get(name) {
            Some(ty) => writeln!(out, "{name}: {ty}").unwrap(),
            None => writeln!(out, "{name}: <missing>").unwrap(),
        }
    }
    out
}

/// A module-level call's result has the type the oracle gives a call of its
/// callee, with every argument unknown: the call is never run, and its
/// arguments are never checked.
#[test]
fn module_call_results_typed() {
    let (errors, lib) = typecheck_only(
        r#"
def make():
    return "s"
"#,
        &[],
    );
    assert_eq!(errors, Vec::<String>::new());

    let (errors, interface) = typecheck_only(
        r#"
load("lib.star", "make")
Lib = record(name = str)
Mode = enum("debug", "release")

def annotated() -> str:
    return "a"

def unannotated():
    return 1

def takes_str(s: str) -> int:
    return len(s)

def rebound() -> str:
    return "r"

early = later()

def later() -> int:
    return 1

cfg = Lib(name = "x")
bad_arg = Lib(name = 1)
mode = Mode("debug")
ann = annotated()
unann = unannotated()
loaded = make()
both = annotated()
both = later()
if len([]) > 0:
    cond = annotated()
else:
    cond = later()
split = "a,b".split(",")
star = annotated(*[], **{})
wrong_arg = takes_str(1)
rebound_call = rebound()
rebound = 1
never = fail("no")
"#,
        &[("lib.star", &lib)],
    );
    assert_eq!(errors, Vec::<String>::new());
    assert_eq!(
        interface_types(
            &interface,
            &[
                "cfg",
                "bad_arg",
                "mode",
                "ann",
                "unann",
                "loaded",
                "both",
                "cond",
                "early",
                "split",
                "star",
                "wrong_arg",
                "rebound_call",
                "never",
            ]
        ),
        "\
cfg: Lib
bad_arg: Lib
mode: Mode
ann: str
unann: typing.Any
loaded: str
both: int | str
cond: typing.Any
early: typing.Any
split: list[str]
star: str
wrong_arg: int
rebound_call: str
never: typing.Never
"
    );
}

/// The right operand of `and`/`or` may never run, so the pre-pass reports
/// nothing in it; the left operand always runs.
#[test]
fn short_circuit_right_operand_unchecked() {
    let code = r#"
Mode = enum("a")
x = False and "s".nope()
y = False and Mode.nope()
z = False and "s".nope
w = True or Mode.nope
"#;
    let (errors, _) = typecheck_only(code, &[]);
    assert_eq!(errors, Vec::<String>::new());
    Module::with_temp_heap(|module| {
        let ast = AstModule::parse("filename", code.to_owned(), &Dialect::Extended).unwrap();
        let globals = Globals::extended_internal();
        let mut eval = Evaluator::new(&module);
        eval.eval_module(ast, &globals).unwrap();
    });

    let (errors, _) = typecheck_only("x = \"s\".nope and True\n", &[]);
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(errors[0].contains("nope"), "{errors:?}");
}

/// A call result has no value, so it is never a type.
#[test]
fn module_call_result_is_not_a_type() {
    let (errors, _) = typecheck_only(
        r#"
Lib = record(name = str)
cfg = Lib(name = "x")
Made = list(["a"])

def f(x: Made, y: cfg):
    pass
"#,
        &[],
    );
    assert_eq!(errors, Vec::<String>::new());
}

#[test]
fn module_call_result_attrs_checked() {
    crate::typing::tests::TypeCheck::new().check(
        "module_call_result_attrs_checked",
        r#"
Lib = record(name = str)
cfg = Lib(name = "x")
parts = "a,b".split(",")

def ok() -> str:
    return cfg.name + parts[0]

def bad():
    cfg.nme

def bad_parts():
    parts.nope
"#,
    );
}

const LIB: &str = r#"
Lib = record(name = str)
Mode = enum("debug", "release")
Names = list[str]
Other = record(name = str)
F = field(str)
cfg = Lib(name = "x")
n = 1
"#;

/// A record, an enum and an alias keep the type they denote through
/// `load()`; a value that is not a type has none.
#[test]
fn loaded_types_work_as_annotations() {
    let (lib, lib_module) = crate::typing::tests::TypeCheck::new().check("loaded_types_lib", LIB);
    let denoted = ["Lib", "Mode", "Names", "Other", "F", "cfg", "n"]
        .iter()
        .map(|name| match lib.get_type(name) {
            Some(ty) => format!("{name}: {ty}\n"),
            None => format!("{name}: -\n"),
        })
        .collect::<String>();
    assert_eq!(
        denoted,
        "Lib: Lib\nMode: Mode\nNames: list[str]\nOther: Other\nF: -\ncfg: -\nn: -\n"
    );

    crate::typing::tests::TypeCheck::new()
        .load("lib.star", lib, lib_module)
        .check(
            "loaded_types_work_as_annotations",
            r#"
load("lib.star", "Lib", "Mode", "Names", L = "Lib")
Libs = list[Lib]
Opt = Lib | None

def ok(l: Lib, m: Mode, n: Names, ls: Libs, o: Opt, a: L) -> str:
    return l.name + m.value + n[0] + ls[0].name + a.name

def bad_record(l: Lib):
    l.nme

def bad_enum(m: Mode):
    m.nope

def bad_alias(n: Names):
    x: int = n[0]

def bad_compound(ls: Libs):
    ls[0].nme
"#,
        );
}

/// I4: one declaration is one type, whichever path loads it; two records with
/// the same fields are two types.
#[test]
fn loaded_record_identity() {
    let (lib, lib_module) =
        crate::typing::tests::TypeCheck::new().check("loaded_record_identity_lib", LIB);
    let (reexport, reexport_module) = crate::typing::tests::TypeCheck::new()
        .load("lib.star", lib.clone(), lib_module.clone())
        .check(
            "loaded_record_identity_reexport",
            r#"
load("lib.star", _Lib = "Lib")
Lib = _Lib
"#,
        );
    crate::typing::tests::TypeCheck::new()
        .load("lib.star", lib, lib_module)
        .load("reexport.star", reexport, reexport_module)
        .check(
            "loaded_record_identity",
            r#"
load("lib.star", "Lib", "Other")
load("reexport.star", Lib2 = "Lib")

def takes(l: Lib):
    pass

def same(l: Lib2):
    takes(l)

def distinct(o: Other):
    takes(o)
"#,
        );
}

/// I8: each binding in a def is reported with the def path that owns it and
/// how it is bound; module bindings separately, private names included.
#[test]
fn bindings_report_owner_and_kind() {
    let ast = AstModule::parse(
        "filename",
        r#"
load("lib.star", _Loaded = "Lib")
Lib = record(name = str)
Lib2 = Lib
Mode = enum("a", "b")
_private = 1

def f(x: int, *args, **kwargs):
    y = x + 1
    for i in range(y):
        pass
    def inner(z: str):
        w = z
        return w
    names = [n for n in ["a"]]
    g = lambda q: q
    return inner

def h(x: str):
    pass
"#
        .to_owned(),
        &Dialect::AllOptionsInternal,
    )
    .unwrap();
    let (_, lib) = typecheck_only("Lib = record(name = str)", &[]);
    let loads = [("lib.star".to_owned(), lib)].into_iter().collect();
    let (errors, typemap, _, _) = ast.typecheck(&super::typecheck_globals(), &loads);
    assert!(errors.is_empty(), "{errors:?}");

    let mut out = String::new();
    for (owner, name, kind, ty) in typemap.bindings() {
        writeln!(out, "{}: {name} {} {ty}", owner.join("."), kind.as_str()).unwrap();
    }
    writeln!(out, "--").unwrap();
    for b in typemap.module_bindings() {
        let as_type = b.as_type.map(|t| t.to_string());
        let declaration = b
            .declaration
            .map(|(_, span)| span.resolve_span().begin.line + 1);
        writeln!(
            out,
            "{}: {} as_type={as_type:?} declared_line={declaration:?}",
            b.name, b.ty
        )
        .unwrap();
    }
    golden_test_template(
        "src/typing/tests/golden/bindings_report_owner_and_kind.golden",
        &out,
    );

    // A record and its alias share one declaration: Lib's.
    let ids: Vec<_> = typemap
        .module_bindings()
        .filter(|b| b.name == "Lib" || b.name == "Lib2")
        .map(|b| b.declaration.map(|(id, _)| id))
        .collect();
    assert_eq!(ids.len(), 2);
    assert!(ids[0].is_some());
    assert_eq!(ids[0], ids[1]);
}
