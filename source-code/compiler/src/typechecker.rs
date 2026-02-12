use crate::ast::*;
use anyhow::Result;
use std::collections::HashMap;

pub struct TypeChecker<'a> {
    pub type_map: &'a HashMap<String, StructOrUnion>,
    pub func_types: &'a HashMap<String, (Vec<HType>, HType)>,
}

impl<'a> TypeChecker<'a> {
    pub fn new(type_map: &'a HashMap<String, StructOrUnion>, func_types: &'a HashMap<String, (Vec<HType>, HType)>) -> Self {
        Self { type_map, func_types }
    }

    pub fn check_expr(&self, expr: &HSharpExpr, env: &[HashMap<String, HType>]) -> Result<HType> {
        match expr {
            HSharpExpr::Literal(lit) => Ok(match lit {
                HSharpLiteral::Int(_) => HType::I32,
                                           HSharpLiteral::Bool(_) => HType::Bool,
                                           HSharpLiteral::String(_) => HType::Struct("String".to_string()),
                                           HSharpLiteral::Float(_) => HType::F64,
            }),
            HSharpExpr::Var(name) => env.iter().rev()
            .find_map(|m| m.get(name))
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("Undefined variable: {}", name)),
            HSharpExpr::Assign(l, r) => {
                let lt = self.check_expr(l, env)?;
                let rt = self.check_expr(r, env)?;
                if lt != rt { return Err(anyhow::anyhow!("Assign type mismatch: {:?} != {:?}", lt, rt)); }
                Ok(lt)
            },
            HSharpExpr::BinOp(op, l, r) => {
                let lt = self.check_expr(l, env)?;
                let rt = self.check_expr(r, env)?;

                if matches!(op, HSharpOp::Add | HSharpOp::Sub) {
                    if let HType::Pointer(_) = lt { if rt == HType::I32 { return Ok(lt); } }
                }

                if lt != rt { return Err(anyhow::anyhow!("Type mismatch {:?} {:?}", lt, rt)); }
                match op {
                    HSharpOp::Eq | HSharpOp::Ne | HSharpOp::Lt | HSharpOp::Gt | HSharpOp::Le | HSharpOp::Ge => Ok(HType::Bool),
                    _ => Ok(lt)
                }
            },
            HSharpExpr::Block(stmts) => {
                let mut local_env = env.to_vec();
                local_env.push(HashMap::new());
                let mut last_type = HType::Unit;

                for stmt in stmts {
                    match stmt {
                        HSharpStmt::Let(name, ty_opt, expr) => {
                            let infer_ty = self.check_expr(expr, &local_env)?;
                            if let Some(ann) = ty_opt {
                                if *ann != infer_ty {
                                    return Err(anyhow::anyhow!("Let type mismatch for {}: expected {:?}, got {:?}", name, ann, infer_ty));
                                }
                            }
                            local_env.last_mut().unwrap().insert(name.clone(), infer_ty);
                            last_type = HType::Unit;
                        },
                        HSharpStmt::Expr(e) => {
                            last_type = self.check_expr(e, &local_env)?;
                        },
                        _ => {
                            last_type = HType::Unit;
                        }
                    }
                }
                Ok(last_type)
            },
            HSharpExpr::Cast(target_ty, _) => Ok(target_ty.clone()),
            HSharpExpr::MethodCall(obj, method, _) => {
                let obj_ty = self.check_expr(obj, env)?;
                let struct_name = match obj_ty {
                    HType::Struct(n) => n,
                    HType::Pointer(b) => match *b { HType::Struct(n) => n, _ => return Err(anyhow::anyhow!("Method on non-struct"))},
                    _ => return Err(anyhow::anyhow!("Method on non-struct"))
                };
                let mangled = format!("{}_{}", struct_name, method);
                if let Some((_, ret)) = self.func_types.get(&mangled) {
                    Ok(ret.clone())
                } else {
                    Err(anyhow::anyhow!("Method not found: {}", method))
                }
            },
            HSharpExpr::If(cond, then_expr, else_expr) => {
                let _ = self.check_expr(cond, env)?;
                let then_ty = self.check_expr(then_expr, env)?;
                if let Some(else_e) = else_expr {
                    let else_ty = self.check_expr(else_e, env)?;
                    if then_ty != else_ty {
                        return Err(anyhow::anyhow!("If branches type mismatch: {:?} vs {:?}", then_ty, else_ty));
                    }
                    Ok(then_ty)
                } else {
                    Ok(HType::Unit)
                }
            },
            HSharpExpr::Match(target, cases, default) => {
                let t_ty = self.check_expr(target, env)?;
                let mut ret_ty = HType::Unit;
                let mut first = true;

                for (cond, body) in cases {
                    // Handle wildcard "_" pattern
                    let is_wildcard = if let HSharpExpr::Var(n) = cond { n == "_" } else { false };

                    if !is_wildcard {
                        let cond_ty = self.check_expr(cond, env)?;
                        if cond_ty != t_ty {
                            return Err(anyhow::anyhow!("Match condition type mismatch: {:?} vs {:?}", t_ty, cond_ty));
                        }
                    }

                    let body_ty = self.check_expr(body, env)?;
                    if first {
                        ret_ty = body_ty;
                        first = false;
                    } else if body_ty != ret_ty {
                        return Err(anyhow::anyhow!("Match arm type mismatch: {:?} vs {:?}", ret_ty, body_ty));
                    }
                }

                if let Some(d) = default {
                    let default_ty = self.check_expr(d, env)?;
                    if !first && default_ty != ret_ty {
                        return Err(anyhow::anyhow!("Match default arm type mismatch"));
                    }
                    ret_ty = default_ty;
                }
                Ok(ret_ty)
            },
            HSharpExpr::Alloc(_) => Ok(HType::Pointer(Box::new(HType::I8))),
            HSharpExpr::Deref(e) => {
                match self.check_expr(e, env)? {
                    HType::Pointer(inner) => Ok(*inner),
                    _ => Err(anyhow::anyhow!("Deref non-pointer"))
                }
            },
            HSharpExpr::AddrOf(e) => {
                let t = self.check_expr(e, env)?;
                Ok(HType::Pointer(Box::new(t)))
            },
            HSharpExpr::Call(name, _) => {
                self.func_types.get(name).map(|(_, r)| r.clone()).ok_or_else(|| anyhow::anyhow!("Fn not found: {}", name))
            },
            HSharpExpr::SizeOf(_) => Ok(HType::I32),
            HSharpExpr::StructLit(name, _) => Ok(HType::Struct(name.clone())),
            HSharpExpr::UnionLit(name, _, _) => Ok(HType::Union(name.clone())),
            HSharpExpr::ArrayLit(elems) => {
                if let Some(first) = elems.first() {
                    let t = self.check_expr(first, env)?;
                    Ok(HType::Array(Box::new(t), elems.len()))
                } else {
                    Ok(HType::Unit)
                }
            },
            HSharpExpr::Index(arr, _) => {
                match self.check_expr(arr, env)? {
                    HType::Array(t, _) | HType::Slice(t) | HType::Pointer(t) => Ok(*t),
                    _ => Err(anyhow::anyhow!("Index on non-array"))
                }
            },
            HSharpExpr::Field(obj, field) => {
                let t = self.check_expr(obj, env)?;
                let struct_name = match t {
                    HType::Struct(n) => n,
                    HType::Pointer(b) => match *b { HType::Struct(n) => n, _ => return Err(anyhow::anyhow!("Field on non-struct"))},
                    _ => return Err(anyhow::anyhow!("Field on non-struct"))
                };
                self.type_map.get(&struct_name).and_then(|s| s.field_type(field)).ok_or_else(|| anyhow::anyhow!("Field not found"))
            },
            HSharpExpr::While(cond, body) => {
                let _ = self.check_expr(cond, env)?;
                let _ = self.check_expr(body, env)?;
                Ok(HType::Unit)
            },
            HSharpExpr::For(var, start, end, body) => {
                let start_ty = self.check_expr(start, env)?;
                if start_ty != HType::I32 { return Err(anyhow::anyhow!("For loop start must be I32")); }
                let _ = self.check_expr(end, env)?;

                let mut loop_env = env.to_vec();
                loop_env.push(HashMap::new());
                loop_env.last_mut().unwrap().insert(var.clone(), HType::I32);
                let _ = self.check_expr(body, &loop_env)?;
                Ok(HType::Unit)
            },
            HSharpExpr::Write(_) => Ok(HType::Unit),
            HSharpExpr::Break => Ok(HType::Unit),
            HSharpExpr::Continue => Ok(HType::Unit),
            HSharpExpr::Direct(_) => Ok(HType::Unit),
            HSharpExpr::Dealloc(_) => Ok(HType::Unit),
            HSharpExpr::Return(_) => Ok(HType::Unit),
        }
    }
}
