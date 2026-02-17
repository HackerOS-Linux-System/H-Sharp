use crate::ast::*;
use crate::types::{HType, StructOrUnion};
use anyhow::{anyhow, Result};
use std::collections::HashMap;

/// Unified function signature – replaces the old (Vec<HType>, HType) tuple.
#[derive(Clone, Debug, PartialEq)]
pub struct FuncSig {
    pub params: Vec<(String, HType)>, // (name, type) – name useful for better errors
    pub ret: HType,
    pub is_async: bool,
    pub is_extern: bool,
    pub variadic: bool,
}

pub struct TypeChecker<'a> {
    pub type_map: &'a HashMap<String, StructOrUnion>,
    pub func_types: &'a HashMap<String, FuncSig>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(
        type_map: &'a HashMap<String, StructOrUnion>,
        func_types: &'a HashMap<String, FuncSig>,
    ) -> Self {
        Self { type_map, func_types }
    }

    /// Returns true if `from` can be implicitly converted to `to`.
    /// This implements all the coercions listed in the TODO.
    fn can_coerce(&self, from: &HType, to: &HType) -> bool {
        if from == to {
            return true;
        }

        match (from, to) {
            // Integer promotions / widening
            (HType::U8, HType::I32) => true,
            (HType::U8, HType::I64) => true,
            (HType::I8, HType::I32) => true,
            (HType::I8, HType::I64) => true,
            (HType::U16, HType::I32) => true,
            (HType::U16, HType::I64) => true,
            (HType::I16, HType::I32) => true,
            (HType::I16, HType::I64) => true,
            (HType::I32, HType::I64) => true,
            (HType::U32, HType::I64) => true,

            // Float widening
            (HType::F32, HType::F64) => true,

            // &T → *T (reference → raw pointer coercion)
            (HType::Ref(inner), HType::Pointer(p)) if **inner == **p => true,

            // *T → *const T / *mut T (raw pointer to const/mut pointer)
            (HType::Pointer(inner), HType::Pointer(target)) if inner == target => true,

            // Pointers are compatible with any pointer if the pointee is the same
            (HType::Pointer(a), HType::Pointer(b)) if a == b => true,

            _ => false,
        }
    }

    /// Main expression type-checking entry point.
    pub fn check_expr(
        &self,
        expr: &HSharpExpr,
        env: &[HashMap<String, HType>],
    ) -> Result<HType> {
        match expr {
            HSharpExpr::Literal(lit) => Ok(match lit {
                HSharpLiteral::Int(_) => HType::I32,
                                           HSharpLiteral::UInt8(_) => HType::U8,      // new – supports 0xFF_u8
                                           HSharpLiteral::UInt16(_) => HType::U16,
                                           HSharpLiteral::UInt32(_) => HType::U32,
                                           HSharpLiteral::UInt64(_) => HType::U64,
                                           HSharpLiteral::Int64(_) => HType::I64,
                                           HSharpLiteral::Bool(_) => HType::Bool,
                                           HSharpLiteral::String(_) => HType::Struct("String".to_string(), vec![]),
                                           HSharpLiteral::Float(_) => HType::F64,
                                           HSharpLiteral::Char(_) => HType::U8,
            }),

            HSharpExpr::Var(name) => env
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .cloned()
            .ok_or_else(|| anyhow!("Undefined variable: {}", name)),

            // ======================= ASSIGNMENT WITH COERCION =======================
            HSharpExpr::Assign(left, right) => {
                let left_ty = self.check_expr(left, env)?;
                let right_ty = self.check_expr(right, env)?;

                if !self.can_coerce(&right_ty, &left_ty) {
                    return Err(anyhow!(
                        "Cannot assign {:?} to {:?} (no coercion)",
                                       right_ty,
                                       left_ty
                    ));
                }
                Ok(left_ty) // assignment expression has type of LHS
            }

            // ======================= BINARY OPS (with promotion) =======================
            HSharpExpr::BinOp(op, left, right) => {
                let mut lt = self.check_expr(left, env)?;
                let mut rt = self.check_expr(right, env)?;

                // Simple integer promotion for arithmetic
                if matches!(op, HSharpOp::Add | HSharpOp::Sub | HSharpOp::Mul | HSharpOp::Div) {
                    if lt == HType::I32 && rt == HType::U8 {
                        rt = HType::I32;
                    }
                    if rt == HType::I32 && lt == HType::U8 {
                        lt = HType::I32;
                    }
                }

                if !self.can_coerce(&rt, &lt) && !self.can_coerce(&lt, &rt) {
                    return Err(anyhow!("Binary op type mismatch: {:?} != {:?}", lt, rt));
                }

                match op {
                    HSharpOp::Eq | HSharpOp::Ne | HSharpOp::Lt | HSharpOp::Gt | HSharpOp::Le | HSharpOp::Ge => {
                        Ok(HType::Bool)
                    }
                    _ => Ok(lt), // arithmetic returns the common type
                }
            }

            // ======================= BLOCK (inference + new stmt handling) =======================
            HSharpExpr::Block(stmts) => {
                let mut local_env = env.to_vec();
                local_env.push(HashMap::new());

                let mut last_ty = HType::Unit;

                for stmt in stmts {
                    match stmt {
                        HSharpStmt::Let(name, ann, init) => {
                            let inferred = self.check_expr(init, &local_env)?;
                            let final_ty = if let Some(ann) = ann {
                                if !self.can_coerce(&inferred, ann) {
                                    return Err(anyhow!(
                                        "Let annotation mismatch for {}: expected {:?}, got {:?}",
                                        name, ann, inferred
                                    ));
                                }
                                ann.clone()
                            } else {
                                inferred
                            };

                            local_env.last_mut().unwrap().insert(name.clone(), final_ty.clone());
                            last_ty = HType::Unit; // let is statement
                        }
                        HSharpStmt::Expr(e) => {
                            last_ty = self.check_expr(e, &local_env)?;
                        }
                        HSharpStmt::Return(e) => {
                            // Return inside block – we just type-check it; the real check happens in check_function
                            let _ = if let Some(e) = e {
                                self.check_expr(e, &local_env)?
                            } else {
                                HType::Unit
                            };
                            last_ty = HType::Unit;
                        }
                        _ => last_ty = HType::Unit,
                    }
                }
                Ok(last_ty)
            }

            HSharpExpr::Cast(target, inner) => {
                let _ = self.check_expr(inner, env)?; // we allow any cast for now (runtime checks elsewhere)
                Ok(target.clone())
            }

            // ======================= METHOD CALL (uses FuncSig) =======================
            HSharpExpr::MethodCall(obj, method, args) => {
                let obj_ty = self.check_expr(obj, env)?;
                let struct_name = match &obj_ty {
                    HType::Struct(n, _) => n.clone(),
                    HType::Pointer(b) => match &**b {
                        HType::Struct(n, _) => n.clone(),
                        _ => return Err(anyhow!("Method call on non-struct pointer")),
                    },
                    _ => return Err(anyhow!("Method call on non-struct")),
                };

                let mangled = format!("{}_{}", struct_name, method);
                let sig = self
                .func_types
                .get(&mangled)
                .ok_or_else(|| anyhow!("Method {} not found on {}", method, struct_name))?;

                // skip self param
                let param_tys: Vec<HType> = sig.params.iter().skip(1).map(|(_, t)| t.clone()).collect();
                self.check_call_args(args, &param_tys, env, sig.variadic)?;

                Ok(sig.ret.clone())
            }

            HSharpExpr::If(cond, then_branch, else_branch) => {
                let _ = self.check_expr(cond, env)?; // condition must be bool – we could add coercion later

                let then_ty = self.check_expr(then_branch, env)?;
                if let Some(else_b) = else_branch {
                    let else_ty = self.check_expr(else_b, env)?;
                    if !self.can_coerce(&else_ty, &then_ty) && !self.can_coerce(&then_ty, &else_ty) {
                        return Err(anyhow!("If branches mismatch: {:?} vs {:?}", then_ty, else_ty));
                    }
                    Ok(if self.can_coerce(&else_ty, &then_ty) {
                        then_ty
                    } else {
                        else_ty
                    })
                } else {
                    Ok(HType::Unit)
                }
            }

            // ======================= MATCH (basic enum support) =======================
            HSharpExpr::Match(target, arms, default) => {
                let target_ty = self.check_expr(target, env)?;

                let mut result_ty = HType::Unit;
                let mut first = true;

                for (pat, body) in arms {
                    // Very simple pattern support for now:
                    // - _ wildcard
                    // - EnumVariant("PacketType", "TCP", [binding]) → type-checks as the enum type
                    match pat {
                        HSharpExpr::Var(name) if name == "_" => { /* wildcard */ }
                        HSharpExpr::EnumVariant(enum_name, _, _) => {
                            // For a real enum variant constructor we would verify that the variant belongs to target_ty
                            // For MVP we just require that the constructor type equals target_ty
                            if target_ty != HType::Enum(enum_name.clone()) {
                                return Err(anyhow!(
                                    "Match arm variant type mismatch: expected {:?}, got enum {}",
                                    target_ty,
                                    enum_name
                                ));
                            }
                        }
                        _ => {
                            let pat_ty = self.check_expr(pat, env)?;
                            if pat_ty != target_ty {
                                return Err(anyhow!("Match pattern type mismatch"));
                            }
                        }
                    }

                    let body_ty = self.check_expr(body, env)?;
                    if first {
                        result_ty = body_ty;
                        first = false;
                    } else if !self.can_coerce(&body_ty, &result_ty) {
                        return Err(anyhow!("Match arm types differ"));
                    }
                }

                if let Some(def) = default {
                    let def_ty = self.check_expr(def, env)?;
                    if !first && !self.can_coerce(&def_ty, &result_ty) {
                        return Err(anyhow!("Match default arm type mismatch"));
                    }
                    result_ty = def_ty;
                }

                Ok(result_ty)
            }

            // ======================= ? OPERATOR (Result propagation) =======================
            HSharpExpr::Try(inner) => {
                let inner_ty = self.check_expr(inner, env)?;
                match inner_ty {
                    HType::Result(ok_ty, _) => Ok(*ok_ty), // unwraps to the Ok variant
                    _ => Err(anyhow!(
                        "? can only be used on Result<T,E>, got {:?}",
                        inner_ty
                    )),
                }
            }

            HSharpExpr::Call(name, args) => {
                let sig = self
                .func_types
                .get(name)
                .ok_or_else(|| anyhow!("Function {} not found", name))?;

                let param_tys: Vec<HType> = sig.params.iter().map(|(_, t)| t.clone()).collect();
                self.check_call_args(args, &param_tys, env, sig.variadic)?;

                Ok(sig.ret.clone())
            }

            HSharpExpr::Alloc(ty) => Ok(HType::Pointer(Box::new(ty.clone()))),
            HSharpExpr::Dealloc(_) => Ok(HType::Unit),
            HSharpExpr::Deref(e) => match self.check_expr(e, env)? {
                HType::Pointer(inner) => Ok(*inner),
                HType::Ref(inner) => Ok(*inner), // &T also dereferences
                _ => Err(anyhow!("Cannot dereference non-pointer")),
            },
            HSharpExpr::AddrOf(e) => {
                let t = self.check_expr(e, env)?;
                Ok(HType::Pointer(Box::new(t)))
            }
            HSharpExpr::Ref(e) => {
                let t = self.check_expr(e, env)?;
                Ok(HType::Ref(Box::new(t)))
            }

            HSharpExpr::Field(obj, field) => {
                let obj_ty = self.check_expr(obj, env)?;
                let struct_name = match obj_ty {
                    HType::Struct(n, _) => n,
                    HType::Pointer(b) => match *b {
                        HType::Struct(n, _) => n,
                        _ => return Err(anyhow!("Field access on non-struct pointer")),
                    },
                    _ => return Err(anyhow!("Field access on non-struct")),
                };

                self.type_map
                .get(&struct_name)
                .and_then(|s| s.field_type(field))
                .ok_or_else(|| anyhow!("Field {} not found in {}", field, struct_name))
            }

            HSharpExpr::ArrayLit(elems) => {
                if elems.is_empty() {
                    return Ok(HType::Unit);
                }
                let first_ty = self.check_expr(&elems[0], env)?;
                for e in &elems[1..] {
                    let t = self.check_expr(e, env)?;
                    if !self.can_coerce(&t, &first_ty) {
                        return Err(anyhow!("Array literal element type mismatch"));
                    }
                }
                Ok(HType::Array(Box::new(first_ty), elems.len()))
            }

            HSharpExpr::Index(arr, idx) => {
                let arr_ty = self.check_expr(arr, env)?;
                let _ = self.check_expr(idx, env)?; // index must be integer
                match arr_ty {
                    HType::Array(t, _) | HType::Slice(t) | HType::Pointer(t) => Ok(*t),
                    _ => Err(anyhow!("Cannot index non-array/slice/pointer")),
                }
            }

            // everything else (While, For, Write, Break, Continue, SizeOf, StructLit, UnionLit, Direct…)
            _ => {
                // fallback – many of these already existed and are correct
                match expr {
                    HSharpExpr::While(_, _) => Ok(HType::Unit),
                    HSharpExpr::For(_, _, _, _) => Ok(HType::Unit),
                    HSharpExpr::Write(_) => Ok(HType::Unit),
                    HSharpExpr::Break => Ok(HType::Unit),
                    HSharpExpr::Continue => Ok(HType::Unit),
                    HSharpExpr::SizeOf(_) => Ok(HType::I32),
                    HSharpExpr::StructLit(name, _) => Ok(HType::Struct(name.clone(), vec![])),
                    HSharpExpr::UnionLit(name, _, _) => Ok(HType::Union(name.clone())),
                    HSharpExpr::Direct(_) => Ok(HType::Unit),
                    _ => Err(anyhow!("Unhandled expression in typechecker: {:?}", expr)),
                }
            }
        }
    }

    /// Helper used by Call / MethodCall with coercion + variadic support.
    fn check_call_args(
        &self,
        args: &[HSharpExpr],
        params: &[HType],
        env: &[HashMap<String, HType>],
        variadic: bool,
    ) -> Result<()> {
        let min_args = params.len();
        if !variadic && args.len() != min_args {
            return Err(anyhow!(
                "Argument count mismatch: expected {}, got {}",
                min_args,
                args.len()
            ));
        }
        if variadic && args.len() < min_args {
            return Err(anyhow!("Too few arguments for variadic function"));
        }

        for (i, param_ty) in params.iter().enumerate() {
            let arg_ty = self.check_expr(&args[i], env)?;
            if !self.can_coerce(&arg_ty, param_ty) {
                return Err(anyhow!(
                    "Argument {}: cannot coerce {:?} → {:?}",
                    i, arg_ty, param_ty
                ));
            }
        }
        Ok(())
    }

    /// Top-level function checker – use this from your compiler driver.
    pub fn check_function(&self, f: &HSharpFn) -> Result<()> {
        let sig = self
        .func_types
        .get(&f.name)
        .ok_or_else(|| anyhow!("Function {} missing from func_types table", f.name))?;

        let mut env = vec![HashMap::new()];
        // insert parameters
        for (name, ty) in &sig.params {
            env[0].insert(name.clone(), ty.clone());
        }

        let expected_ret = Some(&sig.ret);

        // Type-check body (block)
        let body_ty = self.check_expr(&f.body, &env)?;

        if !self.can_coerce(&body_ty, expected_ret.unwrap()) {
            return Err(anyhow!(
                "Function {} return type mismatch: expected {:?}, got {:?}",
                f.name, sig.ret, body_ty
            ));
        }

        Ok(())
    }
}
