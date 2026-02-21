use crate::ast::{HSharpExpr, HSharpLiteral, HSharpOp, HSharpStmt, HType};
use crate::types::StructOrUnion;
use anyhow::{anyhow, Result};
use std::collections::HashMap;
/// Unified function signature.
#[derive(Clone, Debug, PartialEq)]
pub struct FuncSig {
    pub params: Vec<(String, HType)>, // (name, type)
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
    fn can_coerce(&self, from: &HType, to: &HType) -> bool {
        if from == to {
            return true;
        }
        match (from, to) {
            // Integer promotions
            (HType::U8, HType::I32) => true,
            (HType::U8, HType::I64) => true,
            (HType::I8, HType::I32) => true,
            (HType::I8, HType::I64) => true,
            (HType::I32, HType::I64) => true,
            (HType::U32, HType::I64) => true,
            // Float widening
            (HType::F32, HType::F64) => true,
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
                                           HSharpLiteral::Float(_) => HType::F64,
                                           HSharpLiteral::Bool(_) => HType::Bool,
                                           HSharpLiteral::String(_) => HType::Struct("String".to_string(), vec![]),
                                           HSharpLiteral::RawString(_) => HType::Struct("String".to_string(), vec![]),
                                           HSharpLiteral::Byte(_) => HType::U8,
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
                Ok(left_ty)
            }
            // ======================= BINARY OPS =======================
            HSharpExpr::BinOp(op, left, right) => {
                let mut lt = self.check_expr(left, env)?;
                let mut rt = self.check_expr(right, env)?;
                // Simple integer promotion
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
                let common_ty = if self.can_coerce(&lt, &rt) { rt.clone() } else { lt.clone() };
                match op {
                    HSharpOp::Eq | HSharpOp::Ne | HSharpOp::Lt | HSharpOp::Gt | HSharpOp::Le | HSharpOp::Ge => {
                        Ok(HType::Bool)
                    }
                    _ => Ok(common_ty),
                }
            }
            // ======================= BLOCK =======================
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
                            last_ty = HType::Unit;
                        }
                        HSharpStmt::Expr(e) => {
                            last_ty = self.check_expr(e, &local_env)?;
                        }
                        _ => last_ty = HType::Unit,
                    }
                }
                Ok(last_ty)
            }
            HSharpExpr::Cast(target, inner) => {
                let _ = self.check_expr(inner, env)?;
                Ok(target.clone())
            }
            // ======================= METHOD CALL =======================
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
                let param_tys: Vec<HType> = sig.params.iter().skip(1).map(|(_, t)| t.clone()).collect();
                self.check_call_args(args, &param_tys, env, sig.variadic)?;
                Ok(sig.ret.clone())
            }
            HSharpExpr::If(cond, then_branch, else_branch) => {
                let _ = self.check_expr(cond, env)?;
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
            // ======================= MATCH =======================
            HSharpExpr::Match(target, arms, default) => {
                let target_ty = self.check_expr(target, env)?;
                let mut result_ty = HType::Unit;
                let mut first = true;
                for (pat, body) in arms {
                    match pat {
                        HSharpExpr::Var(name) if name == "_" => { /* wildcard */ }
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
            HSharpExpr::Try(inner) => {
                let inner_ty = self.check_expr(inner, env)?;
                match inner_ty {
                    HType::Result(ok_ty, _) => Ok(*ok_ty),
                    _ => Err(anyhow!("? can only be used on Result<T,E>, got {:?}", inner_ty)),
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
            HSharpExpr::Alloc(inner_expr) => {
                let ty = self.check_expr(inner_expr, env)?;
                Ok(HType::Pointer(Box::new(ty)))
            }
            HSharpExpr::Dealloc(_) => Ok(HType::Unit),
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
                let _ = self.check_expr(idx, env)?;
                match arr_ty {
                    HType::Array(t, _) | HType::Slice(t) | HType::Pointer(t) => Ok(*t),
                    _ => Err(anyhow!("Cannot index non-array/slice/pointer")),
                }
            }
            // Fallback for expression variants not yet implemented or missing in local AST copy
            _ => Ok(HType::Unit),
        }
    }
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
                    "Argument {}: cannot coerce {:?} to {:?}",
                    i, arg_ty, param_ty
                ));
            }
        }
        Ok(())
    }
    pub fn check_function_body(
        &self,
        name: &str,
        params: &Vec<(String, HType)>,
                               ret: &HType,
                               body: &HSharpExpr,
    ) -> Result<()> {
        let sig = self
        .func_types
        .get(name)
        .ok_or_else(|| anyhow!("Function {} missing from func_types table", name))?;
        let mut env = vec![HashMap::new()];
        for (name, ty) in &sig.params {
            env[0].insert(name.clone(), ty.clone());
        }
        let body_ty = self.check_expr(body, &env)?;
        if !self.can_coerce(&body_ty, &sig.ret) {
            return Err(anyhow!(
                "Function {} return type mismatch: expected {:?}, got {:?}",
                name, sig.ret, body_ty
            ));
        }
        Ok(())
    }
}
