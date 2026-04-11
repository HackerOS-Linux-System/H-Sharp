use std::collections::HashMap;

/// A memory region — corresponds to one `is...end` block
#[derive(Debug, Clone)]
pub struct Region {
    pub id:       RegionId,
    pub parent:   Option<RegionId>,
    pub values:   Vec<RegionValue>,
    pub kind:     RegionKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionId(pub u32);

#[derive(Debug, Clone)]
pub enum RegionKind {
    /// Normal scope (fn body, if/for/while block)
    Scope,
    /// Arena — bulk-free all at once (unsafe arena(N) is...end)
    Arena { size: usize },
    /// Manual — raw malloc/free (unsafe manual is...end)
    Manual,
    /// Function call frame
    Frame,
}

/// A value tracked by a region
#[derive(Debug, Clone)]
pub struct RegionValue {
    pub name:     String,
    pub ty:       RegionType,
    pub owned:    bool,    // true = this region owns + will drop
    pub moved:    bool,    // true = moved out, don't drop
}

#[derive(Debug, Clone, PartialEq)]
pub enum RegionType {
    Scalar,          // int, float, bool — stack only, no drop
    String,          // heap-allocated string — needs drop
    Bytes,           // heap bytes — needs drop
    Struct(String),  // named struct — needs drop if has Drop impl
    Array(Box<RegionType>),
    Ptr,             // raw pointer in unsafe
}

impl RegionType {
    pub fn needs_drop(&self) -> bool {
        matches!(self, RegionType::String | RegionType::Bytes
                     | RegionType::Struct(_) | RegionType::Array(_))
    }
}

/// Region stack — tracks active regions during compilation
#[derive(Debug, Default)]
pub struct RegionStack {
    regions: HashMap<RegionId, Region>,
    stack:   Vec<RegionId>,
    next_id: u32,
}

impl RegionStack {
    pub fn new() -> Self { Self::default() }

    /// Enter a new scope region
    pub fn push_scope(&mut self) -> RegionId {
        self.push(RegionKind::Scope)
    }

    pub fn push_arena(&mut self, size: usize) -> RegionId {
        self.push(RegionKind::Arena { size })
    }

    pub fn push_frame(&mut self) -> RegionId {
        self.push(RegionKind::Frame)
    }

    fn push(&mut self, kind: RegionKind) -> RegionId {
        let id = RegionId(self.next_id);
        self.next_id += 1;
        let parent = self.stack.last().copied();
        self.regions.insert(id, Region {
            id, parent, values: Vec::new(), kind,
        });
        self.stack.push(id);
        id
    }

    /// Exit current scope — returns values that need dropping
    pub fn pop(&mut self) -> Vec<RegionValue> {
        if let Some(id) = self.stack.pop() {
            if let Some(region) = self.regions.remove(&id) {
                // Return values that are owned and not moved (need drop code)
                return region.values.into_iter()
                    .filter(|v| v.owned && !v.moved && v.ty.needs_drop())
                    .collect();
            }
        }
        Vec::new()
    }

    /// Register a new value in the current scope
    pub fn declare(&mut self, name: &str, ty: RegionType) {
        if let Some(&id) = self.stack.last() {
            if let Some(region) = self.regions.get_mut(&id) {
                region.values.push(RegionValue {
                    name: name.to_string(),
                    ty,
                    owned: true,
                    moved: false,
                });
            }
        }
    }

    /// Mark a value as moved (transferred ownership)
    pub fn mark_moved(&mut self, name: &str) {
        for id in self.stack.iter().rev() {
            if let Some(region) = self.regions.get_mut(id) {
                if let Some(v) = region.values.iter_mut().find(|v| v.name == name) {
                    v.moved = true;
                    return;
                }
            }
        }
    }

    /// Check if a value is accessible (not moved, in scope)
    pub fn is_accessible(&self, name: &str) -> bool {
        for id in self.stack.iter().rev() {
            if let Some(region) = self.regions.get(id) {
                if let Some(v) = region.values.iter().find(|v| v.name == name) {
                    return !v.moved;
                }
            }
        }
        false
    }

    /// Current region kind (for unsafe detection)
    pub fn current_kind(&self) -> Option<&RegionKind> {
        self.stack.last()
            .and_then(|id| self.regions.get(id))
            .map(|r| &r.kind)
    }

    pub fn in_unsafe(&self) -> bool {
        self.stack.iter().rev().any(|id| {
            self.regions.get(id).map(|r| matches!(
                r.kind, RegionKind::Arena { .. } | RegionKind::Manual
            )).unwrap_or(false)
        })
    }
}

/// Generate drop/free code comment for interpreter/codegen
/// In Cranelift backend: replaced with actual free() calls
pub fn drop_hint(value: &RegionValue) -> String {
    match &value.ty {
        RegionType::String   => format!("hsh_string_drop(&{})", value.name),
        RegionType::Bytes    => format!("hsh_bytes_drop(&{})", value.name),
        RegionType::Struct(n) => format!("{}_drop(&{})", n, value.name),
        RegionType::Array(_) => format!("hsh_array_drop(&{})", value.name),
        _ => String::new(),
    }
}
