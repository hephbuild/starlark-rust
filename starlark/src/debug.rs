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

//! Provides debug-related functionality and utilities.
// hephbuild: the Debug Adapter Protocol types (`debugserver-types`, whose
// schemafy codegen is one of the slowest proc macros in an embedder's build)
// are behind the `dap` feature, off by default.
#[cfg(feature = "dap")]
mod adapter;

mod evaluate;
mod inspect;

#[cfg(feature = "dap")]
pub use adapter::*;
