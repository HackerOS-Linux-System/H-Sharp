use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum RegionKind {
    Scope,
    Arena { size: usize },
    Manual,
    Frame,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RegionTy {
    Scalar,          // int/float/bool — no drop
    StringVal,       // heap string  → hsh_string_free(ptr)
    BytesVal,        // heap bytes   → hsh_bytes_free(ptr)
    Struct(String),  // named struct → StructName_drop(ptr)
    Array(Box<RegionTy>),
}

impl RegionTy {
    pub fn needs_drop(&self) -> bool {
        !matches!(self, RegionTy::Scalar)
    }

    /// C runtime function name that frees this type
    pub fn drop_fn(&self) -> Option<&'static str> {
        match self {
            RegionTy::StringVal => Some("hsh_string_free"),
            RegionTy::BytesVal  => Some("hsh_bytes_free"),
            RegionTy::Array(_)  => Some("hsh_array_free"),
            _                   => None,
        }
    }

    pub fn from_type_name(name: &str) -> Self {
        match name {
            "string"              => RegionTy::StringVal,
            "bytes"               => RegionTy::BytesVal,
            "int"|"uint"|"bool"|"f64"|"f32"|
            "i8"|"i16"|"i32"|"i64"|"i128"|
            "u8"|"u16"|"u32"|"u64"|"u128" => RegionTy::Scalar,
            other                 => RegionTy::Struct(other.to_string()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RegionValue {
    pub name:   String,
    pub ty:     RegionTy,
    pub moved:  bool,  // moved out — skip drop
}

#[derive(Debug, Clone)]
pub struct Region {
    pub id:     RegionId,
    pub parent: Option<RegionId>,
    pub kind:   RegionKind,
    values:     Vec<RegionValue>,
}

#[derive(Debug, Default)]
pub struct RegionStack {
    regions: HashMap<RegionId, Region>,
    stack:   Vec<RegionId>,
    next_id: u32,
}

impl RegionStack {
    pub fn new() -> Self { Self::default() }

    pub fn push_scope(&mut self) -> RegionId  { self.push(RegionKind::Scope) }
    pub fn push_frame(&mut self) -> RegionId  { self.push(RegionKind::Frame) }
    pub fn push_arena(&mut self, sz: usize) -> RegionId { self.push(RegionKind::Arena { size: sz }) }

    fn push(&mut self, kind: RegionKind) -> RegionId {
        let id = RegionId(self.next_id);
        self.next_id += 1;
        self.regions.insert(id, Region {
            id, parent: self.stack.last().copied(), kind, values: Vec::new(),
        });
        self.stack.push(id);
        id
    }

    /// Exit current scope.  Returns (kind, values_needing_drop).
    pub fn pop(&mut self) -> (RegionKind, Vec<RegionValue>) {
        if let Some(id) = self.stack.pop() {
            if let Some(region) = self.regions.remove(&id) {
                let kind = region.kind.clone();
                let drops: Vec<RegionValue> = region.values.into_iter()
                    .filter(|v| !v.moved && v.ty.needs_drop())
                    .collect();
                return (kind, drops);
            }
        }
        (RegionKind::Scope, Vec::new())
    }

    /// Register a new `let` binding in the current scope.
    pub fn declare(&mut self, name: &str, ty: RegionTy) {
        if let Some(&id) = self.stack.last() {
            if let Some(r) = self.regions.get_mut(&id) {
                r.values.push(RegionValue { name: name.to_string(), ty, moved: false });
            }
        }
    }

    /// Mark a value as moved (ownership transferred — skip drop).
    pub fn mark_moved(&mut self, name: &str) {
        for id in self.stack.iter().rev() {
            if let Some(r) = self.regions.get_mut(id) {
                if let Some(v) = r.values.iter_mut().find(|v| v.name == name) {
                    v.moved = true;
                    return;
                }
            }
        }
    }

    pub fn in_unsafe(&self) -> bool {
        self.stack.iter().rev().any(|id|
            self.regions.get(id).map(|r|
                matches!(r.kind, RegionKind::Arena { .. } | RegionKind::Manual)
            ).unwrap_or(false)
        )
    }
}
