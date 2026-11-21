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

//! Return types inferred for top-level `def`s without a return annotation.

use crate::typing::tests::TypeCheck;

#[test]
fn test_infer_return_from_returns() {
    TypeCheck::new().ty("x").check(
        "infer_return_from_returns",
        r#"
def f(n: int):
    return n + 1

def g():
    x = f(1)

def h():
    s: str = f(1)
"#,
    );
}

#[test]
fn test_infer_return_union_with_fall_through() {
    TypeCheck::new().ty("x").ty("y").check(
        "infer_return_union_with_fall_through",
        r#"
def bare(n: int):
    if n > 0:
        return "pos"
    return

def falls(n: int):
    if n > 0:
        return "pos"

def g():
    x = bare(1)
    y = falls(1)

def h():
    n: int = falls(1)
"#,
    );
}

#[test]
fn test_infer_return_if_else_does_not_fall_through() {
    TypeCheck::new().ty("x").check(
        "infer_return_if_else_does_not_fall_through",
        r#"
def f(n: int):
    if n > 0:
        return "pos"
    else:
        return "neg"

def g():
    x = f(1)
"#,
    );
}

#[test]
fn test_infer_return_recursive() {
    TypeCheck::new().ty("x").check(
        "infer_return_recursive",
        r#"
def count(n: int):
    if n == 0:
        return 0
    return count(n - 1) + 1

def g():
    x = count(3)
"#,
    );
}

#[test]
fn test_infer_return_callee_defined_later() {
    TypeCheck::new().ty("x").check(
        "infer_return_callee_defined_later",
        r#"
def g():
    x = outer()

def outer():
    return [inner()]

def inner():
    return "s"
"#,
    );
}

#[test]
fn test_infer_return_fail_is_never() {
    TypeCheck::new().ty("x").check(
        "infer_return_fail_is_never",
        r#"
def boom():
    fail("no")

def g():
    x = boom()
    s: str = boom()
"#,
    );
}

#[test]
fn test_infer_return_nested_def_returns_are_not_the_outer() {
    TypeCheck::new().ty("x").check(
        "infer_return_nested_def_returns_are_not_the_outer",
        r#"
def outer():
    def inner():
        return 1
    return "s"

def g():
    x = outer()
"#,
    );
}

#[test]
fn test_infer_return_annotation_wins() {
    TypeCheck::new().ty("x").check(
        "infer_return_annotation_wins",
        r#"
def f(n: int) -> typing.Any:
    return n

def g():
    x = f(1)
"#,
    );
}

#[test]
fn test_infer_return_through_load() {
    let (interface, module) = TypeCheck::new().check(
        "infer_return_through_load_0",
        r#"
def make_name(n: int):
    return str(n)
"#,
    );
    TypeCheck::new()
        .load("names.bzl", interface, module)
        .ty("x")
        .check(
            "infer_return_through_load_1",
            r#"
load("names.bzl", "make_name")
def g():
    x = make_name(1)
    n: int = make_name(1)
"#,
        );
}

#[test]
fn test_infer_return_def_bound_twice_is_not_inferred() {
    // Both `def`s have the same signature, so both match the declared type;
    // neither one's returns may decide the type of the name.
    TypeCheck::new().check(
        "infer_return_def_bound_twice_is_not_inferred",
        r#"
def f():
    return 1

def f():
    return "s"

def use():
    s: str = f()
"#,
    );
}
