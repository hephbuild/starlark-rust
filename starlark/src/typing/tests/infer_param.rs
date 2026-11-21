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

//! Types inferred for unannotated parameters from a literal default.

use crate::typing::tests::TypeCheck;

#[test]
fn test_infer_param_from_literal_default() {
    TypeCheck::new()
        .ty("i")
        .ty("neg")
        .ty("fl")
        .ty("s")
        .ty("b")
        .ty("l")
        .ty("d")
        .ty("t")
        .check(
            "infer_param_from_literal_default",
            r#"
def f(n = 1, m = -2, x = 1.5, y = "a", z = True, xs = ["a"], kv = {}, tu = ()):
    i = n
    neg = m
    fl = x
    s = y
    b = z
    l = xs
    d = kv
    t = tu
"#,
        );
}

#[test]
fn test_infer_param_checks_the_body() {
    TypeCheck::new().check(
        "infer_param_checks_the_body",
        r#"
def f(n = 1):
    s: str = n
"#,
    );
}

#[test]
fn test_infer_param_checks_callers() {
    TypeCheck::new().check(
        "infer_param_checks_callers",
        r#"
def f(n = 1, xs = []):
    pass

def g():
    f(2, [1])
    f(xs = ["a"])
    f("a")
"#,
    );
}

#[test]
fn test_infer_param_none_default_is_any() {
    TypeCheck::new().ty("v").check(
        "infer_param_none_default_is_any",
        r#"
def f(x = None):
    v = x

def g():
    f(1)
    f("a")
"#,
    );
}

#[test]
fn test_infer_param_non_literal_default_is_any() {
    TypeCheck::new().check(
        "infer_param_non_literal_default_is_any",
        r#"
D = 1

def f(x = D, y = 1 + 1, z = len("a")):
    pass

def g():
    f("a", "b", "c")
"#,
    );
}

#[test]
fn test_infer_param_annotation_wins() {
    TypeCheck::new().check(
        "infer_param_annotation_wins",
        r#"
def f(x: typing.Any = 1, *args, **kwargs):
    pass

def g():
    f("a")
"#,
    );
}
