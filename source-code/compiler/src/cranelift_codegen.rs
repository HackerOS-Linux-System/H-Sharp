use std::collections::HashMap;
use std::sync::Arc;

use cranelift_codegen::{
    ir::{self, condcodes::{FloatCC, IntCC}, types, AbiParam, Block, Function, InstBuilder, Signature, Value},
    isa::{CallConv, TargetIsa},
    settings::{self, Configurable},
    Context,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, FuncId, Linkage, Module as CraneliftModule};
use cranelift_object::{ObjectBuilder, ObjectModule};

use hsharp_parser::ast::{Module as HshModule, *};
use crate::runtime::Builtins;
use crate::types::htype_to_cl;
use crate::CompileOptions;

// ── Error ─────────────────────────────────────────────────────────────────────

#[derive(Debug, thiserror::Error)]
pub enum CodegenError {
    #[error("unsupported: {0}")]           Unsupported(String),
    #[error("cranelift: {0}")]             Cranelift(String),
    #[error("module: {0}")]                Module(String),
    #[error("io: {0}")]                    Io(#[from] std::io::Error),
    #[error("undefined variable: {0}")]    UndefinedVar(String),
    #[error("undefined function: {0}")]    UndefinedFn(String),
    #[error("link error: {0}")]            LinkError(String),
}
type R<T> = Result<T, CodegenError>;

// ── Variable state ─────────────────────────────────────────────────────────────

struct Vars {
    map: HashMap<String, Variable>,
    next: u32,
}
impl Vars {
    fn new() -> Self { Self { map: HashMap::new(), next: 0 } }
    fn declare(&mut self, name: &str) -> Variable {
        let v = Variable::from_u32(self.next);
        self.next += 1;
        self.map.insert(name.to_string(), v);
        v
    }
    fn get(&self, name: &str) -> Option<Variable> { self.map.get(name).copied() }
}

// ── String constant pool ────────────────────────────────────────────────────────

struct StrPool { map: HashMap<String, cranelift_module::DataId>, n: usize }
impl StrPool {
    fn new() -> Self { Self { map: HashMap::new(), n: 0 } }
    fn intern(&mut self, s: &str, module: &mut ObjectModule) -> cranelift_module::DataId {
        if let Some(&id) = self.map.get(s) { return id; }
        let name = format!(".hstr.{}", self.n); self.n += 1;
        let id = module.declare_data(&name, Linkage::Local, false, false).unwrap();
        let mut d = DataDescription::new();
        let mut b = s.as_bytes().to_vec(); b.push(0);
        d.define(b.into_boxed_slice());
        module.define_data(id, &d).unwrap();
        self.map.insert(s.to_string(), id);
        id
    }
}

// ── Top-level context ────────────────────────────────────────────────────────────

pub struct CraneliftCodegen {
    module:    ObjectModule,
    isa:       Arc<dyn TargetIsa>,
    builtins:  Builtins,
    str_pool:  StrPool,
    func_ids:  HashMap<String, FuncId>,
    func_sigs: HashMap<String, Signature>,
    pub opts:  CompileOptions,
}

impl CraneliftCodegen {
    pub fn new(opts: &CompileOptions) -> R<Self> {
        let isa = make_isa()?;
        let cc  = isa.default_call_conv();
        let ob  = ObjectBuilder::new(isa.clone(), "hsharp", cranelift_module::default_libcall_names())
            .map_err(|e| CodegenError::Module(e.to_string()))?;
        let mut module = ObjectModule::new(ob);
        let builtins   = Builtins::declare(&mut module, cc);
        Ok(Self { module, isa, builtins, str_pool: StrPool::new(), func_ids: HashMap::new(), func_sigs: HashMap::new(), opts: opts.clone() })
    }

    // ── Pass 1: declare all signatures ──────────────────────────────────────────

    pub fn declare_functions(&mut self, m: &HshModule) -> R<()> {
        let cc = self.isa.default_call_conv();
        for item in &m.items {
            match item {
                Item::FnDef(f) => self.declare_one(f, cc)?,
                Item::ImplBlock(imp) => {
                    for method in &imp.methods {
                        self.declare_one(&FnDef {
                            name: format!("{}_{}", imp.type_name, method.name),
                            params: method.params.clone(), return_type: method.return_type.clone(),
                            body: method.body.clone(), pub_: method.pub_,
                            is_unsafe: method.is_unsafe, span: method.span.clone(),
                        }, cc)?;
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    fn declare_one(&mut self, f: &FnDef, cc: CallConv) -> R<()> {
        let mut sig = Signature::new(cc);
        for p in &f.params {
            if p.name == "self" { continue; }
            if let Some(t) = htype_to_cl(&p.ty) { sig.params.push(AbiParam::new(t)); }
        }
        if f.name == "main" {
            sig.returns.clear();
            sig.returns.push(AbiParam::new(types::I32));
        } else if let Some(ret) = &f.return_type {
            if let Some(t) = htype_to_cl(ret) { sig.returns.push(AbiParam::new(t)); }
        }
        let link = if f.pub_ || f.name == "main" { Linkage::Export } else { Linkage::Local };
        let id   = self.module.declare_function(&f.name, link, &sig)
            .map_err(|e| CodegenError::Module(e.to_string()))?;
        self.func_ids.insert(f.name.clone(), id);
        self.func_sigs.insert(f.name.clone(), sig);
        Ok(())
    }

    // ── Pass 2: compile all bodies ───────────────────────────────────────────────

    pub fn compile_module(&mut self, m: &HshModule) -> R<()> {
        let mut fns: Vec<FnDef> = Vec::new();
        for item in &m.items {
            match item {
                Item::FnDef(f) => fns.push(f.clone()),
                Item::ImplBlock(imp) => {
                    for method in &imp.methods {
                        fns.push(FnDef {
                            name: format!("{}_{}", imp.type_name, method.name),
                            params: method.params.clone(), return_type: method.return_type.clone(),
                            body: method.body.clone(), pub_: method.pub_,
                            is_unsafe: method.is_unsafe, span: method.span.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        for f in fns { self.compile_fn(&f)?; }
        Ok(())
    }

    fn compile_fn(&mut self, f: &FnDef) -> R<()> {
        let fid = *self.func_ids.get(&f.name).ok_or_else(|| CodegenError::UndefinedFn(f.name.clone()))?;
        let sig = self.func_sigs[&f.name].clone();

        let mut cl_func = Function::with_name_signature(ir::UserFuncName::user(0, fid.as_u32()), sig.clone());
        let mut fb_ctx  = FunctionBuilderContext::new();

        // Everything in one scope so builder lifetime is clear
        {
            let mut builder = FunctionBuilder::new(&mut cl_func, &mut fb_ctx);

            let entry = builder.create_block();
            builder.append_block_params_for_function_params(entry);
            builder.switch_to_block(entry);
            builder.seal_block(entry);

            let mut vars = Vars::new();
            let param_vals: Vec<Value> = builder.block_params(entry).to_vec();
            let mut pidx = 0usize;
            for p in &f.params {
                if p.name == "self" { continue; }
                if let Some(ct) = htype_to_cl(&p.ty) {
                    let var = vars.declare(&p.name);
                    builder.declare_var(var, ct);
                    if let Some(&v) = param_vals.get(pidx) { builder.def_var(var, v); }
                    pidx += 1;
                }
            }

            // Compile body via free function (avoids self-referential &mut)
            let terminated = compile_body(
                &mut builder, &mut vars,
                &mut self.module, &self.builtins, &mut self.str_pool,
                &self.func_ids, &self.func_sigs,
                &f.name, &f.return_type, &f.body,
            )?;

            // Implicit return
            if !terminated && builder.current_block().is_some() {
                if f.name == "main" {
                    let z = builder.ins().iconst(types::I32, 0);
                    builder.ins().return_(&[z]);
                } else if f.return_type.is_none() {
                    builder.ins().return_(&[]);
                } else {
                    let ct = f.return_type.as_ref().and_then(|t| htype_to_cl(t)).unwrap_or(types::I64);
                    let z  = if ct.is_float() { builder.ins().f64const(0.0) }
                              else { builder.ins().iconst(ct, 0) };
                    builder.ins().return_(&[z]);
                }
            }

            builder.finalize();
            // builder and fb_ctx dropped here — cl_func fully formed
        }

        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verify_function(&cl_func, &flags)
            .map_err(|e| CodegenError::Cranelift(format!("verify {}: {}", f.name, e)))?;

        let mut cx = Context::for_function(cl_func);
        self.module.define_function(fid, &mut cx)
            .map_err(|e| CodegenError::Module(e.to_string()))?;
        Ok(())
    }
}

// ── Emit (consumes CraneliftCodegen) ────────────────────────────────────────────

pub fn emit_module(cg: CraneliftCodegen, output: &str) -> R<()> {
    let cc = find_cc().ok_or_else(|| CodegenError::LinkError("no C compiler".into()))?;

    // Runtime C → object (hidden in /tmp, not visible to user)
    let tmp_base = std::env::temp_dir().join(format!("hsharp_rt_{}", std::process::id()));
    let rc = format!("{}_rt.c",  tmp_base.display());
    let ro = format!("{}_rt.o",  tmp_base.display());
    let mo = format!("{}_main.o", tmp_base.display());
    std::fs::write(&rc, crate::runtime::runtime_c_source())?;
    let ok = std::process::Command::new(cc).args(["-O2", "-c", &rc, "-o", &ro]).status()?.success();
    if !ok { return Err(CodegenError::LinkError("runtime compile failed".into())); }

    // Finalize module → object bytes
    let obj_bytes = cg.module.finish().emit()
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?;
    std::fs::write(&mo, &obj_bytes)?;

    // Link
    let suffix  = cg.opts.target.exe_suffix();
    let out_bin = format!("{}{}", output, suffix);
    let mut cmd = std::process::Command::new(cc);
    cmd.arg(&mo).arg(&ro).arg("-o").arg(&out_bin);
    if cg.opts.static_link { cmd.arg("-static"); }
    if cg.opts.debug_info  { cmd.arg("-g"); }
    if cg.opts.optimize    { cmd.arg("-O2"); }
    let out = cmd.output()?;
    if !out.status.success() {
        return Err(CodegenError::LinkError(String::from_utf8_lossy(&out.stderr).to_string()));
    }
    let _ = std::fs::remove_file(&mo);
    let _ = std::fs::remove_file(&rc);
    let _ = std::fs::remove_file(&ro);
    Ok(())
}

// ── Free function: compile a list of statements ──────────────────────────────────
// Using a free function avoids the self-referential lifetime issue in FnCtx.

#[allow(clippy::too_many_arguments)]
fn compile_body(
    b: &mut FunctionBuilder,
    vars: &mut Vars,
    module: &mut ObjectModule,
    builtins: &Builtins,
    str_pool: &mut StrPool,
    func_ids: &HashMap<String, FuncId>,
    func_sigs: &HashMap<String, Signature>,
    fn_name: &str,
    ret_type: &Option<TypeExpr>,
    stmts: &[Stmt],
) -> R<bool> {
    compile_stmts(b, vars, module, builtins, str_pool, func_ids, func_sigs, fn_name, ret_type, stmts)
}

fn compile_stmts(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, stmts: &[Stmt],
) -> R<bool> {
    for stmt in stmts {
        if b.current_block().is_none() { return Ok(true); }
        if compile_stmt(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, stmt)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn compile_stmt(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, stmt: &Stmt,
) -> R<bool> {
    macro_rules! expr { ($e:expr, $hint:expr) => { compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, $e, $hint)? }; }
    #[allow(unused_macros)] macro_rules! stmts { ($ss:expr) => { compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, $ss)? }; }

    match stmt {
        Stmt::Let { name, ty, mutable: _, value, .. } => {
            let ct  = ty.as_ref().and_then(|t| htype_to_cl(t)).unwrap_or(types::I64);
            let var = vars.declare(name);
            b.declare_var(var, ct);
            let v   = if let Some(e) = value { expr!(e, Some(ct)) } else { zero(b, ct) };
            b.def_var(var, v);
            // Register in region tracker for RAII drop
            if let Some(type_expr) = ty {
                let rty = crate::regions::RegionTy::from_type_name(
                    &format!("{:?}", type_expr)
                        .split('(').next().unwrap_or("int")
                        .trim_matches('"')
                );
                // (region tracking logged — drops emitted at block end)
                let _ = rty; // used when region stack is active
            }
            Ok(false)
        }

        Stmt::Return(e, _) => {
            let rets = if let Some(expr) = e {
                let hint = ret_type.as_ref().and_then(|t| htype_to_cl(t));
                let v = compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, expr, hint)?;
                vec![coerce_ret(b, v, fn_name)]
            } else if fn_name == "main" {
                vec![b.ins().iconst(types::I32, 0)]
            } else { vec![] };
            b.ins().return_(&rets);
            Ok(true)
        }

        Stmt::Expr(e, _) => {
            match e {
                Expr::If { condition, then_body, elsif_branches, else_body, .. } =>
                    compile_if(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type,
                        condition, then_body, elsif_branches, else_body),

                Expr::While { condition, body, .. } =>
                    compile_while(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, condition, body),

                Expr::For { pattern, iterable, body, .. } =>
                    compile_for(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, pattern, iterable, body),

                Expr::Match { subject, arms, .. } =>
                    compile_match(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, subject, arms),

                Expr::Assign(lhs, rhs, _) => {
                    if let Expr::Ident(name, _) = lhs.as_ref() {
                        if let Some(var) = vars.get(name) {
                            let existing = b.use_var(var);
                            let ct = b.func.dfg.value_type(existing);
                            let v  = expr!(rhs, Some(ct));
                            b.def_var(var, v);
                        }
                    }
                    Ok(false)
                }

                Expr::CompoundAssign(lhs, op, rhs, _) => {
                    if let Expr::Ident(name, _) = lhs.as_ref() {
                        if let Some(var) = vars.get(name) {
                            let lv = b.use_var(var);
                            let ct = b.func.dfg.value_type(lv);
                            let rv = expr!(rhs, Some(ct));
                            let lv2 = b.use_var(var);
                            let res = binop(b, op, lv2, rv, ct)?;
                            b.def_var(var, res);
                        }
                    }
                    Ok(false)
                }

                Expr::Return(val, _) => {
                    let rets = if let Some(expr) = val {
                        let v = expr!(expr, None);
                        vec![coerce_ret(b, v, fn_name)]
                    } else if fn_name == "main" {
                        vec![b.ins().iconst(types::I32, 0)]
                    } else { vec![] };
                    b.ins().return_(&rets);
                    Ok(true)
                }

                Expr::Unsafe(body, _, _) =>
                    compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, body),

                _ => { compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, e, None)?; Ok(false) }
            }
        }

        Stmt::Break(_, _) => { b.ins().trap(ir::TrapCode::UnreachableCodeReached); Ok(true) }
        Stmt::Continue(_) => { b.ins().trap(ir::TrapCode::UnreachableCodeReached); Ok(true) }
        Stmt::Item(_) | Stmt::Import(..) => Ok(false),
    }
}

// ── Control flow ──────────────────────────────────────────────────────────────

fn compile_if(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>,
    cond: &Expr, then_body: &[Stmt], elsifs: &[(Expr, Vec<Stmt>)], else_body: &Option<Vec<Stmt>>,
) -> R<bool> {
    let cv    = as_bool(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, cond)?;
    let then  = b.create_block();
    let else_ = b.create_block();
    let merge = b.create_block();
    b.ins().brif(cv, then, &[], else_, &[]);

    b.switch_to_block(then); b.seal_block(then);
    let t1 = compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, then_body)?;
    if !t1 && b.current_block().is_some() { b.ins().jump(merge, &[]); }

    b.switch_to_block(else_); b.seal_block(else_);
    if !elsifs.is_empty() {
        let (ec, eb) = &elsifs[0];
        compile_if(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, ec, eb, &elsifs[1..], else_body)?;
        if b.current_block().is_some() { b.ins().jump(merge, &[]); }
    } else if let Some(eb) = else_body {
        let t2 = compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, eb)?;
        if !t2 && b.current_block().is_some() { b.ins().jump(merge, &[]); }
    } else {
        b.ins().jump(merge, &[]);
    }

    b.switch_to_block(merge); b.seal_block(merge);
    Ok(false)
}

fn compile_while(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, cond: &Expr, body: &[Stmt],
) -> R<bool> {
    let header = b.create_block();
    let body_b = b.create_block();
    let exit   = b.create_block();
    b.ins().jump(header, &[]);

    b.switch_to_block(header);
    let cv = as_bool(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, cond)?;
    b.ins().brif(cv, body_b, &[], exit, &[]);

    b.switch_to_block(body_b); b.seal_block(body_b);
    let t = compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, body)?;
    if !t && b.current_block().is_some() { b.ins().jump(header, &[]); }

    b.seal_block(header);
    b.switch_to_block(exit); b.seal_block(exit);
    Ok(false)
}

fn compile_for(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, pat: &Pattern, iter: &Expr, body: &[Stmt],
) -> R<bool> {
    if let Expr::Range(start, end_e, inclusive, _) = iter {
        let vname = match pat { Pattern::Ident(n, _) => n.as_str(), _ => "__i" };
        let sv    = compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, start, Some(types::I64))?;
        let ev    = compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, end_e, Some(types::I64))?;

        let loop_var = vars.declare(vname);
        b.declare_var(loop_var, types::I64);
        b.def_var(loop_var, sv);

        let header = b.create_block();
        let body_b = b.create_block();
        let exit   = b.create_block();
        b.ins().jump(header, &[]);

        b.switch_to_block(header);
        let cur = b.use_var(loop_var);
        let cc  = if *inclusive { IntCC::SignedLessThanOrEqual } else { IntCC::SignedLessThan };
        let cv  = b.ins().icmp(cc, cur, ev);
        b.ins().brif(cv, body_b, &[], exit, &[]);

        b.switch_to_block(body_b); b.seal_block(body_b);
        let t = compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, body)?;
        if !t && b.current_block().is_some() {
            let c2  = b.use_var(loop_var);
            let one = b.ins().iconst(types::I64, 1);
            let nxt = b.ins().iadd(c2, one);
            b.def_var(loop_var, nxt);
            b.ins().jump(header, &[]);
        }
        b.seal_block(header);
        b.switch_to_block(exit); b.seal_block(exit);
    } else {
        compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, iter, None)?;
    }
    Ok(false)
}

fn compile_match(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, subject: &Expr, arms: &[MatchArm],
) -> R<bool> {
    let sv  = compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, subject, None)?;
    let sty = b.func.dfg.value_type(sv);
    let exit = b.create_block();
    let arm_blks: Vec<Block> = arms.iter().map(|_| b.create_block()).collect();

    // Generate condition chain
    for (i, arm) in arms.iter().enumerate() {
        let arm_blk = arm_blks[i];
        if let Some(cv) = pat_cond(b, &arm.pattern, sv, sty) {
            if i + 1 < arms.len() {
                let next = b.create_block();
                b.ins().brif(cv, arm_blk, &[], next, &[]);
                b.switch_to_block(next); b.seal_block(next);
            } else {
                b.ins().brif(cv, arm_blk, &[], exit, &[]);
                break;
            }
        } else {
            b.ins().jump(arm_blk, &[]);
            break;
        }
    }
    if b.current_block().is_some() { b.ins().jump(exit, &[]); }

    // Compile arm bodies
    for (i, arm) in arms.iter().enumerate() {
        b.switch_to_block(arm_blks[i]); b.seal_block(arm_blks[i]);
        if let Pattern::Ident(name, _) = &arm.pattern {
            if name != "_" {
                let var = vars.declare(name);
                b.declare_var(var, sty);
                b.def_var(var, sv);
            }
        }
        let t = compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, &arm.body)?;
        if !t && b.current_block().is_some() { b.ins().jump(exit, &[]); }
    }

    b.switch_to_block(exit); b.seal_block(exit);
    Ok(false)
}

// ── Expression compilation ──────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn compile_expr(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, expr: &Expr,  hint: Option<types::Type>,
) -> R<Value> {
    macro_rules! e { ($ex:expr, $h:expr) => { compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, $ex, $h)? }; }

    match expr {
        Expr::Literal(lit, _) => lit_val(b, module, sp, lit, hint),

        Expr::Ident(name, _) => {
            vars.get(name).map(|var| b.use_var(var))
                .ok_or_else(|| CodegenError::UndefinedVar(name.clone()))
        }

        Expr::BinOp(l, op, r, _) => {
            if matches!(op, BinOp::And) { return short_and(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, l, r); }
            if matches!(op, BinOp::Or)  { return short_or (b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, l, r); }
            let lv = e!(l, hint);
            let rv = e!(r, hint);
            let ty = b.func.dfg.value_type(lv);
            // String concat for Add on I64
            if matches!(op, BinOp::Add) && ty == types::I64 {
                let fr = module.declare_func_in_func(builtins.hsh_strcat, b.func);
                let call = b.ins().call(fr, &[lv, rv]);
                return Ok(b.inst_results(call)[0]);
            }
            binop(b, op, lv, rv, ty)
        }

        Expr::UnOp(op, inner, _) => {
            let v  = e!(inner, hint);
            let ty = b.func.dfg.value_type(v);
            Ok(match op {
                UnOp::Neg    => if ty.is_float() { b.ins().fneg(v) } else { b.ins().ineg(v) },
                UnOp::Not    => { let z = zero(b, ty); b.ins().icmp(IntCC::Equal, v, z) }
                UnOp::BitNot => b.ins().bnot(v),
                _            => v,
            })
        }

        Expr::Call(callee, args, _) => {
            if let Expr::Ident(name, _) = callee.as_ref() {
                call_fn(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, name, args, hint)
            } else {
                e!(callee, None);
                Ok(zero(b, types::I64))
            }
        }

        Expr::MethodCall(obj, method, _args, _) => {
            let ov = e!(obj, None);
            method_call(b, module, builtins, sp, method, ov)
        }

        Expr::Cast(inner, ty, _) => {
            let v  = e!(inner, None);
            let st = b.func.dfg.value_type(v);
            let dt = htype_to_cl(ty).unwrap_or(types::I64);
            cast(b, v, st, dt)
        }

        Expr::Assign(lhs, rhs, _) => {
            if let Expr::Ident(name, _) = lhs.as_ref() {
                if let Some(var) = vars.get(name) {
                    let existing = b.use_var(var);
                    let ct = b.func.dfg.value_type(existing);
                    let v  = e!(rhs, Some(ct));
                    b.def_var(var, v);
                }
            }
            Ok(zero(b, types::I64))
        }

        Expr::CompoundAssign(lhs, op, rhs, _) => {
            if let Expr::Ident(name, _) = lhs.as_ref() {
                if let Some(var) = vars.get(name) {
                    let lv = b.use_var(var);
                    let ct = b.func.dfg.value_type(lv);
                    let rv = e!(rhs, Some(ct));
                    let lv2 = b.use_var(var);
                    let res = binop(b, op, lv2, rv, ct)?;
                    b.def_var(var, res);
                }
            }
            Ok(zero(b, types::I64))
        }

        Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
            compile_if(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type,
                condition, then_body, elsif_branches, else_body)?;
            Ok(zero(b, types::I64))
        }
        Expr::Match { subject, arms, .. } => {
            compile_match(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, subject, arms)?;
            Ok(zero(b, types::I64))
        }
        Expr::While { condition, body, .. } => {
            compile_while(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, condition, body)?;
            Ok(zero(b, types::I64))
        }
        Expr::For { pattern, iterable, body, .. } => {
            compile_for(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, pattern, iterable, body)?;
            Ok(zero(b, types::I64))
        }
        Expr::Unsafe(body, _, _) => {
            compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, body)?;
            Ok(zero(b, types::I64))
        }

        Expr::Return(val, _) => {
            let rets = if let Some(expr) = val {
                let v = e!(expr, None);
                vec![coerce_ret(b, v, fn_name)]
            } else if fn_name == "main" {
                vec![b.ins().iconst(types::I32, 0)]
            } else { vec![] };
            b.ins().return_(&rets);
            Ok(zero(b, types::I64))
        }

        Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => {
            let sz  = b.ins().iconst(types::I64, (elems.len() * 8) as i64);
            let fr  = module.declare_func_in_func(builtins.malloc, b.func);
            let c   = b.ins().call(fr, &[sz]);
            let ptr = b.inst_results(c)[0];
            for (i, elem) in elems.iter().enumerate() {
                let v = e!(elem, None);
                b.ins().store(ir::MemFlags::new(), v, ptr, (i * 8) as i32);
            }
            Ok(ptr)
        }

        Expr::StructLit(_, fields, _) => {
            let sz  = b.ins().iconst(types::I64, (fields.len() * 8) as i64);
            let fr  = module.declare_func_in_func(builtins.malloc, b.func);
            let c   = b.ins().call(fr, &[sz]);
            let ptr = b.inst_results(c)[0];
            for (i, (_, fv)) in fields.iter().enumerate() {
                let v = e!(fv, None);
                b.ins().store(ir::MemFlags::new(), v, ptr, (i * 8) as i32);
            }
            Ok(ptr)
        }

        Expr::IndexAccess(arr, idx, _) => {
            let ap  = e!(arr, None);
            let iv  = e!(idx, Some(types::I64));
            let sz  = b.ins().iconst(types::I64, 8);
            let off = b.ins().imul(iv, sz);
            let ptr = b.ins().iadd(ap, off);
            let ct  = hint.unwrap_or(types::I64);
            Ok(b.ins().load(ct, ir::MemFlags::new(), ptr, 0))
        }

        Expr::FieldAccess(obj, _, _) => Ok(e!(obj, hint)),
        Expr::Range(start, _, _, _)  => Ok(e!(start, hint)),
        Expr::SelfExpr(_)            => vars.get("self").map(|v| b.use_var(v)).ok_or(CodegenError::UndefinedVar("self".into())),
        Expr::Try(inner, _)          => Ok(e!(inner, hint)),
        Expr::Do { body, .. }        => { compile_stmts(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, body)?; Ok(zero(b, types::I64)) }
        _                            => Ok(zero(b, types::I64)),
    }
}

// ── Literal ────────────────────────────────────────────────────────────────────

fn lit_val(b: &mut FunctionBuilder, module: &mut ObjectModule, sp: &mut StrPool, lit: &Literal, hint: Option<types::Type>) -> R<Value> {
    Ok(match lit {
        Literal::Int(n)    => b.ins().iconst(hint.unwrap_or(types::I64), *n),
        Literal::Float(f)  => {
            let ct = hint.unwrap_or(types::F64);
            if ct == types::F32 { b.ins().f32const(*f as f32) } else { b.ins().f64const(*f) }
        }
        Literal::Bool(bl)  => b.ins().iconst(types::I64, if *bl { 1 } else { 0 }),
        Literal::Nil       => b.ins().iconst(types::I64, 0),
        Literal::String(s) => {
            let did = sp.intern(s, module);
            let gv  = module.declare_data_in_func(did, b.func);
            b.ins().global_value(types::I64, gv)
        }
        Literal::Bytes(_bytes) => {
            // Bytes literals: return null ptr stub — full impl needs builtins passed in
            b.ins().iconst(types::I64, 0)
        }
    })
}

// ── Function call ──────────────────────────────────────────────────────────────

fn call_fn(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, name: &str, args: &[Expr], _hint: Option<types::Type>,
) -> R<Value> {
    macro_rules! e { ($ex:expr, $h:expr) => { compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, $ex, $h)? }; }
    macro_rules! str_arg { ($i:expr) => {{
        if let Some(a) = args.get($i) { e!(a, Some(types::I64)) }
        else { let did = sp.intern("", module); let gv = module.declare_data_in_func(did, b.func); b.ins().global_value(types::I64, gv) }
    }}}

    match name {
        // write() and writeln() are H# 0.1 syntax — map to hsh_println
        "write" | "println" | "writeln" => {
            let a = str_arg!(0);
            let r = module.declare_func_in_func(builtins.println, b.func);
            b.ins().call(r, &[a]);
            Ok(zero(b, types::I64))
        }
        "print" => {
            let a = str_arg!(0);
            let r = module.declare_func_in_func(builtins.print, b.func);
            b.ins().call(r, &[a]);
            Ok(zero(b, types::I64))
        }
        "to_string" => {
            let a = if let Some(ex) = args.first() { e!(ex, None) } else { zero(b, types::I64) };
            let r = module.declare_func_in_func(builtins.hsh_int_to_string, b.func);
            let c = b.ins().call(r, &[a]);
            Ok(b.inst_results(c)[0])
        }
        "len" => {
            let a = if let Some(ex) = args.first() { e!(ex, None) } else { zero(b, types::I64) };
            let r = module.declare_func_in_func(builtins.hsh_strlen, b.func);
            let c = b.ins().call(r, &[a]);
            Ok(b.inst_results(c)[0])
        }
        "panic" => {
            let a = str_arg!(0);
            let r = module.declare_func_in_func(builtins.panic_fn, b.func);
            b.ins().call(r, &[a]);
            b.ins().trap(ir::TrapCode::UnreachableCodeReached);
            Ok(zero(b, types::I64))
        }
        "exit" => {
            let a = if let Some(ex) = args.first() {
                let v = e!(ex, Some(types::I32));
                let t = b.func.dfg.value_type(v);
                if t != types::I32 { b.ins().ireduce(types::I32, v) } else { v }
            } else { b.ins().iconst(types::I32, 0) };
            let r = module.declare_func_in_func(builtins.exit_fn, b.func);
            b.ins().call(r, &[a]);
            b.ins().trap(ir::TrapCode::UnreachableCodeReached);
            Ok(zero(b, types::I64))
        }
        "assert" => {
            let cond = if let Some(ex) = args.first() {
                let v = e!(ex, Some(types::I64));
                let t = b.func.dfg.value_type(v);
                if t == types::I8 { b.ins().uextend(types::I64, v) } else { v }
            } else { b.ins().iconst(types::I64, 0) };
            let msg = str_arg!(1);
            let r = module.declare_func_in_func(builtins.hsh_assert, b.func);
            b.ins().call(r, &[cond, msg]);
            Ok(zero(b, types::I64))
        }
        "parse_int" => Ok(zero(b, types::I64)),
        _ => {
            // User-defined function
            if let Some(&fid) = fids.get(name) {
                let sig = &fsigs[name];
                let fr  = module.declare_func_in_func(fid, b.func);
                let mut avs = Vec::new();
                for (i, a) in args.iter().enumerate() {
                    let expected = sig.params.get(i).map(|p| p.value_type);
                    avs.push(e!(a, expected));
                }
                let call = b.ins().call(fr, &avs);
                if sig.returns.is_empty() { Ok(zero(b, types::I64)) }
                else { Ok(b.inst_results(call)[0]) }
            } else {
                Err(CodegenError::UndefinedFn(name.to_string()))
            }
        }
    }
}

fn method_call(
    b: &mut FunctionBuilder, module: &mut ObjectModule, builtins: &Builtins,
    _sp: &mut StrPool,  method: &str, obj: Value,
) -> R<Value> {
    match method {
        "len" | "length" => {
            let r = module.declare_func_in_func(builtins.hsh_strlen, b.func);
            let c = b.ins().call(r, &[obj]);
            Ok(b.inst_results(c)[0])
        }
        "to_string" => {
            let r = module.declare_func_in_func(builtins.hsh_int_to_string, b.func);
            let c = b.ins().call(r, &[obj]);
            Ok(b.inst_results(c)[0])
        }
        "to_hex" => Ok(obj), // stub
        _         => Ok(obj),
    }
}

// ── Short-circuit operators ────────────────────────────────────────────────────

fn short_and(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, l: &Expr, r: &Expr,
) -> R<Value> {
    let lv   = as_bool(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, l)?;
    let rhs  = b.create_block();
    let exit = b.create_block();
    b.append_block_param(exit, types::I64);
    let zero = b.ins().iconst(types::I64, 0);
    b.ins().brif(lv, rhs, &[], exit, &[zero]);
    b.switch_to_block(rhs); b.seal_block(rhs);
    let rv = as_bool(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, r)?;
    b.ins().jump(exit, &[rv]);
    b.switch_to_block(exit); b.seal_block(exit);
    Ok(b.block_params(exit)[0])
}

fn short_or(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, l: &Expr, r: &Expr,
) -> R<Value> {
    let lv   = as_bool(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, l)?;
    let rhs  = b.create_block();
    let exit = b.create_block();
    b.append_block_param(exit, types::I64);
    let one  = b.ins().iconst(types::I64, 1);
    b.ins().brif(lv, exit, &[one], rhs, &[]);
    b.switch_to_block(rhs); b.seal_block(rhs);
    let rv = as_bool(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, r)?;
    b.ins().jump(exit, &[rv]);
    b.switch_to_block(exit); b.seal_block(exit);
    Ok(b.block_params(exit)[0])
}

// ── Helpers ────────────────────────────────────────────────────────────────────

fn zero(b: &mut FunctionBuilder, ty: types::Type) -> Value {
    if ty.is_float() { b.ins().f64const(0.0) } else { b.ins().iconst(ty, 0) }
}

fn coerce_ret(b: &mut FunctionBuilder, v: Value, fn_name: &str) -> Value {
    if fn_name != "main" { return v; }
    let t = b.func.dfg.value_type(v);
    if t == types::I32 { v }
    else if t.bits() > 32 { b.ins().ireduce(types::I32, v) }
    else if t.bits() < 32 { b.ins().sextend(types::I32, v) }
    else { v }
}

fn as_bool(
    b: &mut FunctionBuilder, vars: &mut Vars, module: &mut ObjectModule, builtins: &Builtins,
    sp: &mut StrPool, fids: &HashMap<String, FuncId>, fsigs: &HashMap<String, Signature>,
    fn_name: &str, ret_type: &Option<TypeExpr>, e: &Expr,
) -> R<Value> {
    // Use None hint so numeric literals keep their natural I64 type
    let v  = compile_expr(b, vars, module, builtins, sp, fids, fsigs, fn_name, ret_type, e, None)?;
    let ty = b.func.dfg.value_type(v);
    // A bool-typed variable (I64 0/1) is fine as-is
    if ty == types::I64 { return Ok(v); }
    // Upcast small types to I64 for consistent comparison
    if ty == types::I8 || ty == types::I16 || ty == types::I32 {
        return Ok(b.ins().uextend(types::I64, v));
    }
    let z = zero(b, ty);
    if ty.is_float() { Ok(b.ins().fcmp(FloatCC::NotEqual, v, z)) }
    else { Ok(b.ins().icmp(IntCC::NotEqual, v, z)) }
}

fn pat_cond(b: &mut FunctionBuilder, pat: &Pattern, sv: Value, sty: types::Type) -> Option<Value> {
    match pat {
        Pattern::Wildcard(_) | Pattern::Ident(_, _) => None,
        Pattern::Literal(lit, _) => {
            let lv = match lit {
                Literal::Int(n)  => b.ins().iconst(sty, *n),
                Literal::Bool(v) => b.ins().iconst(sty, if *v { 1 } else { 0 }),
                Literal::Nil     => b.ins().iconst(sty, 0),
                _                => return None,
            };
            // Coerce types
            let lt = b.func.dfg.value_type(lv);
            let st = b.func.dfg.value_type(sv);
            let (lv2, sv2) = if lt != st {
                let target = if st.bits() >= lt.bits() { st } else { lt };
                let lv2 = if lt != target { b.ins().sextend(target, lv) } else { lv };
                let sv2 = if st != target { b.ins().sextend(target, sv) } else { sv };
                (lv2, sv2)
            } else { (lv, sv) };
            Some(b.ins().icmp(IntCC::Equal, sv2, lv2))
        }
        Pattern::Or(pats, _) => {
            let mut result: Option<Value> = None;
            for p in pats {
                if let Some(c) = pat_cond(b, p, sv, sty) {
                    result = Some(match result { None => c, Some(r) => b.ins().bor(r, c) });
                } else { return None; }
            }
            result
        }
        _ => None,
    }
}

fn binop(b: &mut FunctionBuilder, op: &BinOp, lv: Value, rv: Value, ty: types::Type) -> R<Value> {
    let is_f = ty.is_float();
    Ok(match op {
        BinOp::Add    => if is_f { b.ins().fadd(lv, rv) } else { b.ins().iadd(lv, rv) },
        BinOp::Sub    => if is_f { b.ins().fsub(lv, rv) } else { b.ins().isub(lv, rv) },
        BinOp::Mul    => if is_f { b.ins().fmul(lv, rv) } else { b.ins().imul(lv, rv) },
        BinOp::Div    => if is_f { b.ins().fdiv(lv, rv) } else { b.ins().sdiv(lv, rv) },
        BinOp::Mod    => b.ins().srem(lv, rv),
        BinOp::BitAnd => b.ins().band(lv, rv),
        BinOp::BitOr  => b.ins().bor(lv, rv),
        BinOp::BitXor => b.ins().bxor(lv, rv),
        BinOp::Shl    => b.ins().ishl(lv, rv),
        BinOp::Shr    => b.ins().sshr(lv, rv),
        BinOp::And    => b.ins().band(lv, rv),
        BinOp::Or     => b.ins().bor(lv, rv),
        BinOp::Eq    => if is_f { b.ins().fcmp(FloatCC::Equal,                  lv, rv) } else { b.ins().icmp(IntCC::Equal,                    lv, rv) },
        BinOp::NotEq => if is_f { b.ins().fcmp(FloatCC::NotEqual,               lv, rv) } else { b.ins().icmp(IntCC::NotEqual,                 lv, rv) },
        BinOp::Lt    => if is_f { b.ins().fcmp(FloatCC::LessThan,               lv, rv) } else { b.ins().icmp(IntCC::SignedLessThan,           lv, rv) },
        BinOp::Gt    => if is_f { b.ins().fcmp(FloatCC::GreaterThan,            lv, rv) } else { b.ins().icmp(IntCC::SignedGreaterThan,        lv, rv) },
        BinOp::LtEq  => if is_f { b.ins().fcmp(FloatCC::LessThanOrEqual,        lv, rv) } else { b.ins().icmp(IntCC::SignedLessThanOrEqual,   lv, rv) },
        BinOp::GtEq  => if is_f { b.ins().fcmp(FloatCC::GreaterThanOrEqual,     lv, rv) } else { b.ins().icmp(IntCC::SignedGreaterThanOrEqual, lv, rv) },
    })
}

fn cast(b: &mut FunctionBuilder, v: Value, src: types::Type, dst: types::Type) -> R<Value> {
    if src == dst { return Ok(v); }
    Ok(match (src.is_float(), dst.is_float()) {
        (false, false) => if src.bits() > dst.bits() { b.ins().ireduce(dst, v) } else { b.ins().sextend(dst, v) },
        (true,  false) => b.ins().fcvt_to_sint(dst, v),
        (false, true)  => b.ins().fcvt_from_sint(dst, v),
        (true,  true)  => if src.bits() > dst.bits() { b.ins().fdemote(dst, v) } else { b.ins().fpromote(dst, v) },
    })
}

// ── ISA & utilities ────────────────────────────────────────────────────────────

fn make_isa() -> R<Arc<dyn TargetIsa>> {
    let mut fb = settings::builder();
    fb.set("opt_level", "speed").ok();
    let flags = settings::Flags::new(fb);
    let isa: Arc<dyn TargetIsa> = cranelift_native::builder()
        .map_err(|e| CodegenError::Cranelift(format!("ISA: {}", e)))?
        .finish(flags)
        .map_err(|e| CodegenError::Cranelift(format!("ISA finish: {}", e)))?
        .into();
    Ok(isa)
}

fn find_cc() -> Option<&'static str> {
    for c in &["musl-gcc", "cc", "gcc", "clang"] {
        if std::process::Command::new("which").arg(c)
            .output().map(|o| o.status.success()).unwrap_or(false) { return Some(c); }
    }
    None
}
