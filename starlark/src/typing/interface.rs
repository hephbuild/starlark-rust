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

use std::collections::HashMap;
use std::sync::Arc;

use dupe::Dupe;

use crate::typing::Ty;

/// Interface representing the types of all bindings in a module.
#[derive(Default, Dupe, Clone, Debug)]
pub struct Interface(Arc<InterfaceData>);

#[derive(Default, Debug)]
struct InterfaceData {
    /// The type of each binding's value.
    bindings: HashMap<String, Ty>,
    /// The type each binding that is a type (a record, an enum or an alias
    /// such as `Names = list[str]`) denotes in a type annotation.
    types: HashMap<String, Ty>,
}

impl Interface {
    /// Create an empty interface, with no bindings.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Create a new interface with the given bindings.
    pub fn new(bindings: HashMap<String, Ty>) -> Self {
        Self::new_with_types(bindings, HashMap::new())
    }

    /// Create a new interface with the given bindings, and the type each
    /// binding that is a type denotes in a type annotation.
    pub fn new_with_types(bindings: HashMap<String, Ty>, types: HashMap<String, Ty>) -> Self {
        Self(Arc::new(InterfaceData { bindings, types }))
    }

    /// Get the type for a given binding.
    pub fn get(&self, name: &str) -> Option<&Ty> {
        self.0.bindings.get(name)
    }

    /// Get the type a given binding denotes in a type annotation, when the
    /// binding is a type (a record, an enum or an alias).
    pub fn get_type(&self, name: &str) -> Option<&Ty> {
        self.0.types.get(name)
    }
}
