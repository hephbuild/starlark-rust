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
use crate::typing::Ty;
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
