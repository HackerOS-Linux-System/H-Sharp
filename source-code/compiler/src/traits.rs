use hsharp_parser::ast::*;
use std::collections::HashMap;

/// Method signature in a trait
#[derive(Debug, Clone)]
pub struct TraitMethod {
    pub name:        String,
    pub params:      Vec<(String, TypeExpr)>,
    pub return_type: Option<TypeExpr>,
}

/// Registered trait definition
#[derive(Debug, Clone)]
pub struct TraitDef2 {
    pub name:    String,
    pub methods: Vec<TraitMethod>,
}

/// An impl block: impl TraitName for TypeName
#[derive(Debug, Clone)]
pub struct ImplRecord {
    pub trait_name: String,
    pub type_name:  String,
    pub methods:    HashMap<String, FnDef>,  // method_name → implementation
}

/// Trait registry — holds all known traits and impls
pub struct TraitRegistry {
    pub traits: HashMap<String, TraitDef2>,
    pub impls:  Vec<ImplRecord>,
}

impl TraitRegistry {
    pub fn new() -> Self {
        Self { traits: HashMap::new(), impls: Vec::new() }
    }

    /// Register a trait definition
    pub fn register_trait(&mut self, def: &TraitDef) {
        let methods = def.methods.iter().map(|m| TraitMethod {
            name:        m.name.clone(),
            params:      m.params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect(),
            return_type: m.return_type.clone(),
        }).collect();
        self.traits.insert(def.name.clone(), TraitDef2 { name: def.name.clone(), methods });
    }

    /// Register an impl block
    pub fn register_impl(&mut self, block: &ImplBlock) {
        if let Some(trait_name) = &block.trait_name {
            let mut methods = HashMap::new();
            for method in &block.methods {
                // Build a FnDef from the method
                let fn_def = FnDef {
                    attrs:       vec![],
                    type_params: vec![],
                    name:        format!("{}__{}__{}", block.type_name, trait_name, method.name),
                    params:      method.params.clone(),
                    return_type: method.return_type.clone(),
                    body:        method.body.clone(),
                    pub_:        method.pub_,
                    is_async:    false,
                    is_unsafe:   method.is_unsafe,
                    span:        method.span.clone(),
                };
                methods.insert(method.name.clone(), fn_def);
            }
            self.impls.push(ImplRecord {
                trait_name: trait_name.clone(),
                type_name:  block.type_name.clone(),
                methods,
            });
        }
    }

    /// Dispatch a method call: given type_name + method_name → mangled FnDef name
    pub fn dispatch(&self, type_name: &str, method_name: &str) -> Option<&FnDef> {
        for impl_rec in &self.impls {
            if impl_rec.type_name == type_name {
                if let Some(fn_def) = impl_rec.methods.get(method_name) {
                    return Some(fn_def);
                }
            }
        }
        None
    }

    /// Check if a type implements a trait
    pub fn implements(&self, type_name: &str, trait_name: &str) -> bool {
        self.impls.iter().any(|i| i.type_name == type_name && i.trait_name == trait_name)
    }

    /// Get all methods for a type (across all impls)
    pub fn all_methods_for(&self, type_name: &str) -> Vec<&FnDef> {
        self.impls.iter()
            .filter(|i| i.type_name == type_name)
            .flat_map(|i| i.methods.values())
            .collect()
    }

    /// Collect all functions to emit (for code generation)
    pub fn emit_fns(&self) -> Vec<&FnDef> {
        self.impls.iter()
            .flat_map(|i| i.methods.values())
            .collect()
    }
}
