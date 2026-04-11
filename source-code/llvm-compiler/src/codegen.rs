use std::collections::HashMap;
use std::path::Path;

use inkwell::{
    AddressSpace,
    OptimizationLevel,
    context::Context,
    builder::Builder,
    module::Module,
    values::{BasicValueEnum, FunctionValue, PointerValue},
    types::{BasicTypeEnum, BasicType},
    targets::{
        CodeModel, FileType, InitializationConfig, RelocMode,
        Target, TargetMachine,
    },
};

use hsharp_parser::ast::{Module as HshModule, *};
use hsharp_compiler::CompileOptions;
use crate::types::htype_to_llvm;
use crate::builtins::LlvmBuiltins;
use crate::optimize::optimize_module;

#[derive(Debug, thiserror::Error)]
pub enum CodegenError {
    #[error("LLVM: {0}")]           Llvm(String),
    #[error("undefined var: {0}")]  UndefinedVar(String),
    #[error("undefined fn: {0}")]   UndefinedFn(String),
    #[error("io: {0}")]             Io(#[from] std::io::Error),
    #[error("link: {0}")]           Link(String),
}
type R<T> = Result<T, CodegenError>;

/// Main LLVM codegen context
pub struct LlvmCodegen {
    context:   Context,
    opts:      CompileOptions,
}

impl LlvmCodegen {
    pub fn new(opts: &CompileOptions) -> R<Self> {
        Target::initialize_x86(&InitializationConfig::default());
        Ok(Self { context: Context::create(), opts: opts.clone() })
    }

    pub fn declare_functions(&mut self, _m: &HshModule) -> R<()> { Ok(()) }
    pub fn compile_module(&mut self, _m: &HshModule) -> R<()> { Ok(()) }

    /// Full compilation: AST → LLVM IR → optimized binary
    pub fn compile_full(&self, m: &HshModule) -> R<()> {
        let ctx = &self.context;
        let module = ctx.create_module("hsharp_module");
        let builder = ctx.create_builder();
        let builtins = LlvmBuiltins::declare(ctx, &module);

        let mut func_vals: HashMap<String, FunctionValue> = HashMap::new();
        let mut str_globals: HashMap<String, PointerValue> = HashMap::new();

        // Pass 1: declare function signatures
        let mut fns = self.collect_fns(m);
        for f in &fns {
            let sig = self.build_fn_type(ctx, f);
            let fv = module.add_function(&f.name, sig, None);
            func_vals.insert(f.name.clone(), fv);
        }

        // Pass 2: compile bodies
        for f in &fns {
            let fv = func_vals[&f.name];
            self.compile_fn(
                ctx, &module, &builder, &builtins, f, fv,
                &func_vals, &mut str_globals,
            )?;
        }

        // Create target machine for optimization
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|e| CodegenError::Llvm(e))?;
        let triple  = TargetMachine::get_default_triple();
        let target  = Target::from_triple(&triple)
            .map_err(|e| CodegenError::Llvm(e.to_string()))?;
        let opt_lvl = if self.opts.optimize { OptimizationLevel::Aggressive } else { OptimizationLevel::Default };

        // Use native CPU with all features for maximum performance (inkwell 0.5)
        let cpu_name    = TargetMachine::get_host_cpu_name();
        let cpu_features = TargetMachine::get_host_cpu_features();

        let machine = target.create_target_machine(
            &triple,
            cpu_name.to_str().unwrap_or("x86-64"),
            cpu_features.to_str().unwrap_or("+avx2,+bmi,+bmi2,+sse4.1,+sse4.2"),
            opt_lvl, RelocMode::PIC, CodeModel::Default,
        ).ok_or_else(|| CodegenError::Llvm("cannot create target machine".into()))?;

        // Apply new pass manager optimizations
        let opt_num = if self.opts.optimize { 3 } else { 1 };
        optimize_module(&module, &machine, opt_num);

        self.emit_binary_with_machine(&module, &machine)

        // Emit
    }

    fn collect_fns<'a>(&self, m: &'a HshModule) -> Vec<FnDef> {
        let mut fns = Vec::new();
        for item in &m.items {
            match item {
                Item::FnDef(f) => fns.push(f.clone()),
                Item::ImplBlock(imp) => {
                    for method in &imp.methods {
                        fns.push(FnDef {
                            name: format!("{}_{}", imp.type_name, method.name),
                            params: method.params.clone(),
                            return_type: method.return_type.clone(),
                            body: method.body.clone(),
                            pub_: method.pub_,
                            is_unsafe: method.is_unsafe,
                            span: method.span.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        fns
    }

    fn build_fn_type<'ctx>(&self, ctx: &'ctx Context, f: &FnDef) -> inkwell::types::FunctionType<'ctx> {
        let mut param_types: Vec<BasicMetadataTypeEnum> = Vec::new();
        for p in &f.params {
            if p.name == "self" { continue; }
            if let Some(t) = htype_to_llvm(ctx, &p.ty) {
                param_types.push(t.into());
            }
        }

        if f.name == "main" {
            return ctx.i32_type().fn_type(&param_types, false);
        }

        match &f.return_type {
            None => ctx.void_type().fn_type(&param_types, false),
            Some(ret) => match htype_to_llvm(ctx, ret) {
                None    => ctx.void_type().fn_type(&param_types, false),
                Some(t) => t.fn_type(&param_types, false),
            }
        }
    }

    fn compile_fn<'ctx>(
        &self,
        ctx:         &'ctx Context,
        module:      &Module<'ctx>,
        builder:     &Builder<'ctx>,
        builtins:    &LlvmBuiltins<'ctx>,
        f:           &FnDef,
        fv:          FunctionValue<'ctx>,
        func_vals:   &HashMap<String, FunctionValue<'ctx>>,
        str_globals: &mut HashMap<String, PointerValue<'ctx>>,
    ) -> R<()> {
        let entry = ctx.append_basic_block(fv, "entry");
        builder.position_at_end(entry);

        let mut vars: HashMap<String, PointerValue<'ctx>> = HashMap::new();

        // Bind parameters
        let mut pidx = 0u32;
        for p in &f.params {
            if p.name == "self" { continue; }
            if let Some(llvm_ty) = htype_to_llvm(ctx, &p.ty) {
                let param_val = fv.get_nth_param(pidx).unwrap();
                let ptr = builder.build_alloca(llvm_ty, &p.name).unwrap();
                builder.build_store(ptr, param_val).unwrap();
                vars.insert(p.name.clone(), ptr);
                pidx += 1;
            }
        }

        let mut cx = FnCx {
            ctx, module, builder, builtins, func_vals, str_globals,
            vars, fn_name: f.name.clone(), ret_type: f.return_type.clone(),
        };

        let terminated = cx.stmts(&f.body)?;

        if !terminated {
            if f.name == "main" {
                let zero = ctx.i32_type().const_int(0, false);
                builder.build_return(Some(&zero)).unwrap();
            } else if f.return_type.is_none() {
                builder.build_return(None).unwrap();
            } else {
                let ct = f.return_type.as_ref().and_then(|t| htype_to_llvm(ctx, t))
                    .unwrap_or(ctx.i64_type().into());
                let zero = self.zero_val(ctx, ct);
                builder.build_return(Some(&zero)).unwrap();
            }
        }

        // Run function-level optimizations
        Ok(())
    }

    fn zero_val<'ctx>(&self, ctx: &'ctx Context, ty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match ty {
            BasicTypeEnum::IntType(t)   => t.const_zero().into(),
            BasicTypeEnum::FloatType(t) => t.const_zero().into(),
            BasicTypeEnum::PointerType(t) => t.const_null().into(),
            _ => ctx.i64_type().const_zero().into(),
        }
    }

    /// Emit binary using a pre-built TargetMachine (from compile_full)
    fn emit_binary_with_machine(&self, module: &Module, machine: &TargetMachine) -> R<()> {
        // Write runtime C
        let rt_c = format!("{}_rt.c", self.opts.output);
        let rt_o = format!("{}_rt.o", self.opts.output);
        std::fs::write(&rt_c, hsharp_compiler::runtime::runtime_c_source())?;
        let ok = std::process::Command::new("cc")
            .args(["-O2", "-c", &rt_c, "-o", &rt_o])
            .status()?.success();
        if !ok { return Err(CodegenError::Link("runtime compile failed".into())); }

        // Emit .o
        let obj_path = format!("{}_main.o", self.opts.output);
        machine.write_to_file(module, FileType::Object, Path::new(&obj_path))
            .map_err(|e| CodegenError::Llvm(e.to_string()))?;

        // Link
        let suffix = self.opts.target.exe_suffix();
        let out = format!("{}{}", self.opts.output, suffix);
        let mut cmd = std::process::Command::new("cc");
        cmd.arg(&obj_path).arg(&rt_o).arg("-o").arg(&out);
        cmd.arg("-no-pie");      // avoid PIE relocation errors on some distros
        if self.opts.static_link { cmd.arg("-static"); }
        else { cmd.arg("-fPIE"); }
        if self.opts.optimize { cmd.arg("-O2"); }
        let result = cmd.output()?;
        if !result.status.success() {
            return Err(CodegenError::Link(
                String::from_utf8_lossy(&result.stderr).to_string()
            ));
        }

        let _ = std::fs::remove_file(&obj_path);
        let _ = std::fs::remove_file(&rt_c);
        let _ = std::fs::remove_file(&rt_o);
        Ok(())
    }

    pub fn emit(&self, _output: &str, _optimize: bool) -> R<()> { Ok(()) }

    pub fn get_ir(&self) -> String { String::new() }

    pub fn emit_object_file(&self, _out: &str) -> R<()> { Ok(()) }
}

// ── Per-function compile context ──────────────────────────────────────────────

use inkwell::types::BasicMetadataTypeEnum;

struct FnCx<'ctx, 'a> {
    ctx:         &'ctx Context,
    module:      &'a Module<'ctx>,
    builder:     &'a Builder<'ctx>,
    builtins:    &'a LlvmBuiltins<'ctx>,
    func_vals:   &'a HashMap<String, FunctionValue<'ctx>>,
    str_globals: &'a mut HashMap<String, PointerValue<'ctx>>,
    vars:        HashMap<String, PointerValue<'ctx>>,
    fn_name:     String,
    ret_type:    Option<TypeExpr>,
}

impl<'ctx, 'a> FnCx<'ctx, 'a> {
    fn stmts(&mut self, stmts: &[Stmt]) -> R<bool> {
        for stmt in stmts {
            if self.stmt(stmt)? { return Ok(true); }
        }
        Ok(false)
    }

    fn stmt(&mut self, s: &Stmt) -> R<bool> {
        match s {
            Stmt::Let { name, ty, mutable: _, value, .. } => {
                let llvm_ty = ty.as_ref()
                    .and_then(|t| htype_to_llvm(self.ctx, t))
                    .unwrap_or(self.ctx.i64_type().into());
                let ptr = self.builder.build_alloca(llvm_ty, name).unwrap();
                if let Some(e) = value {
                    let v = self.expr(e, Some(llvm_ty))?;
                    self.builder.build_store(ptr, v).unwrap();
                } else {
                    let zero = self.zero(llvm_ty);
                    self.builder.build_store(ptr, zero).unwrap();
                }
                self.vars.insert(name.clone(), ptr);
                Ok(false)
            }

            Stmt::Return(e, _) => {
                let ret = if let Some(expr) = e {
                    let hint = self.ret_type.as_ref().and_then(|t| htype_to_llvm(self.ctx, t));
                    let v = self.expr(expr, hint)?;
                    let v = self.coerce_ret(v);
                    self.builder.build_return(Some(&v)).unwrap();
                } else if self.fn_name == "main" {
                    let z = self.ctx.i32_type().const_int(0, false);
                    self.builder.build_return(Some(&z)).unwrap();
                } else {
                    self.builder.build_return(None).unwrap();
                };
                Ok(true)
            }

            Stmt::Expr(e, _) => {
                match e {
                    Expr::If { condition, then_body, elsif_branches, else_body, .. } =>
                        self.if_stmt(condition, then_body, elsif_branches, else_body),

                    Expr::While { condition, body, .. } =>
                        self.while_stmt(condition, body),

                    Expr::For { pattern, iterable, body, .. } =>
                        self.for_stmt(pattern, iterable, body),

                    Expr::Assign(lhs, rhs, _) => {
                        if let Expr::Ident(name, _) = lhs.as_ref() {
                            if let Some(&ptr) = self.vars.get(name.as_str()) {
                                let ty = Some(BasicTypeEnum::IntType(self.ctx.i64_type()));
                                let v = self.expr(rhs, ty)?;
                                self.builder.build_store(ptr, v).unwrap();
                            }
                        }
                        Ok(false)
                    }

                    Expr::CompoundAssign(lhs, op, rhs, _) => {
                        if let Expr::Ident(name, _) = lhs.as_ref() {
                            if let Some(&ptr) = self.vars.get(name.as_str()) {
                                                let lv = self.builder.build_load(
                                    self.ctx.i64_type(),
                                    ptr, "lv"
                                ).unwrap();
                                let rv = self.expr(rhs, None)?;
                                let res = self.binop(op, lv, rv)?;
                                self.builder.build_store(ptr, res).unwrap();
                            }
                        }
                        Ok(false)
                    }

                    Expr::Return(val, _) => {
                        if let Some(expr) = val {
                            let v = self.expr(expr, None)?;
                            let v = self.coerce_ret(v);
                            self.builder.build_return(Some(&v)).unwrap();
                        } else if self.fn_name == "main" {
                            let z = self.ctx.i32_type().const_int(0, false);
                            self.builder.build_return(Some(&z)).unwrap();
                        } else {
                            self.builder.build_return(None).unwrap();
                        }
                        Ok(true)
                    }

                    _ => { self.expr(e, None)?; Ok(false) }
                }
            }

            Stmt::Break(_, _) | Stmt::Continue(_) => {
                self.builder.build_unreachable().unwrap();
                Ok(true)
            }
            Stmt::Item(_) | Stmt::Import(..) => Ok(false),
        }
    }

    // ── Control flow ──────────────────────────────────────────────────────────

    fn if_stmt(&mut self, cond: &Expr, then_b: &[Stmt],
                elsifs: &[(Expr, Vec<Stmt>)], else_b: &Option<Vec<Stmt>>) -> R<bool> {
        let parent = self.builder.get_insert_block().unwrap()
            .get_parent().unwrap();
        let cv = self.as_bool(cond)?;

        let then_blk  = self.ctx.append_basic_block(parent, "then");
        let else_blk  = self.ctx.append_basic_block(parent, "else");
        let merge_blk = self.ctx.append_basic_block(parent, "merge");

        self.builder.build_conditional_branch(cv, then_blk, else_blk).unwrap();

        self.builder.position_at_end(then_blk);
        let t1 = self.stmts(then_b)?;
        if !t1 { self.builder.build_unconditional_branch(merge_blk).unwrap(); }

        self.builder.position_at_end(else_blk);
        if !elsifs.is_empty() {
            let (ec, eb) = &elsifs[0];
            self.if_stmt(ec, eb, &elsifs[1..], else_b)?;
            if self.builder.get_insert_block().map(|b| b.get_terminator().is_none()).unwrap_or(false) {
                self.builder.build_unconditional_branch(merge_blk).unwrap();
            }
        } else if let Some(eb) = else_b {
            let t2 = self.stmts(eb)?;
            if !t2 { self.builder.build_unconditional_branch(merge_blk).unwrap(); }
        } else {
            self.builder.build_unconditional_branch(merge_blk).unwrap();
        }

        self.builder.position_at_end(merge_blk);
        Ok(false)
    }

    fn while_stmt(&mut self, cond: &Expr, body: &[Stmt]) -> R<bool> {
        let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
        let header = self.ctx.append_basic_block(parent, "while_hdr");
        let body_b = self.ctx.append_basic_block(parent, "while_body");
        let exit   = self.ctx.append_basic_block(parent, "while_exit");

        self.builder.build_unconditional_branch(header).unwrap();
        self.builder.position_at_end(header);
        let cv = self.as_bool(cond)?;
        self.builder.build_conditional_branch(cv, body_b, exit).unwrap();

        self.builder.position_at_end(body_b);
        let t = self.stmts(body)?;
        if !t { self.builder.build_unconditional_branch(header).unwrap(); }

        self.builder.position_at_end(exit);
        Ok(false)
    }

    fn for_stmt(&mut self, pat: &Pattern, iter: &Expr, body: &[Stmt]) -> R<bool> {
        if let Expr::Range(start, end_e, inclusive, _) = iter {
            let vname = match pat { Pattern::Ident(n, _) => n.as_str(), _ => "__i" };
            let i64t  = self.ctx.i64_type();

            let sv = self.expr(start, Some(i64t.into()))?;
            let ev = self.expr(end_e,  Some(i64t.into()))?;

            let loop_ptr = self.builder.build_alloca(i64t, vname).unwrap();
            self.builder.build_store(loop_ptr, sv).unwrap();
            self.vars.insert(vname.to_string(), loop_ptr);

            let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
            let header = self.ctx.append_basic_block(parent, "for_hdr");
            let body_b = self.ctx.append_basic_block(parent, "for_body");
            let exit   = self.ctx.append_basic_block(parent, "for_exit");

            self.builder.build_unconditional_branch(header).unwrap();
            self.builder.position_at_end(header);

            let cur = self.builder.build_load(i64t, loop_ptr, "cur").unwrap();
            let cond = if *inclusive {
                self.builder.build_int_compare(
                    inkwell::IntPredicate::SLE, cur.into_int_value(), ev.into_int_value(), "cmp"
                ).unwrap()
            } else {
                self.builder.build_int_compare(
                    inkwell::IntPredicate::SLT, cur.into_int_value(), ev.into_int_value(), "cmp"
                ).unwrap()
            };
            self.builder.build_conditional_branch(cond, body_b, exit).unwrap();

            self.builder.position_at_end(body_b);
            let t = self.stmts(body)?;
            if !t {
                let c2  = self.builder.build_load(i64t, loop_ptr, "c2").unwrap().into_int_value();
                let one = i64t.const_int(1, false);
                let nxt = self.builder.build_int_add(c2, one, "nxt").unwrap();
                self.builder.build_store(loop_ptr, nxt).unwrap();
                self.builder.build_unconditional_branch(header).unwrap();
            }

            self.builder.position_at_end(exit);
        } else {
            self.expr(iter, None)?;
        }
        Ok(false)
    }

    // ── Expressions ───────────────────────────────────────────────────────────

    fn expr(&mut self, e: &Expr, hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
        match e {
            Expr::Literal(lit, _) => self.literal(lit, hint),

            Expr::Ident(name, _) => {
                let ptr = self.vars.get(name.as_str())
                    .copied()
                    .ok_or_else(|| CodegenError::UndefinedVar(name.clone()))?;
                Ok(self.builder.build_load(self.ctx.i64_type(), ptr, name).unwrap())
            }

            Expr::BinOp(l, op, r, _) => {
                let lv = self.expr(l, hint)?;
                let rv = self.expr(r, hint)?;
                self.binop(op, lv, rv)
            }

            Expr::UnOp(op, inner, _) => {
                let v = self.expr(inner, hint)?;
                match op {
                    UnOp::Neg => match v {
                        BasicValueEnum::IntValue(i)   => Ok(self.builder.build_int_neg(i, "neg").unwrap().into()),
                        BasicValueEnum::FloatValue(f) => Ok(self.builder.build_float_neg(f, "fneg").unwrap().into()),
                        _ => Ok(v),
                    },
                    UnOp::Not => {
                        let i = v.into_int_value();
                        let zero = i.get_type().const_zero();
                        Ok(self.builder.build_int_compare(inkwell::IntPredicate::EQ, i, zero, "not").unwrap().into())
                    }
                    _ => Ok(v),
                }
            }

            Expr::Call(callee, args, _) => {
                if let Expr::Ident(name, _) = callee.as_ref() {
                    self.call_fn(name, args, hint)
                } else {
                    Ok(self.ctx.i64_type().const_zero().into())
                }
            }

            Expr::Assign(lhs, rhs, _) => {
                if let Expr::Ident(name, _) = lhs.as_ref() {
                    if let Some(&ptr) = self.vars.get(name.as_str()) {
                            let v = self.expr(rhs, None)?;
                        self.builder.build_store(ptr, v).unwrap();
                    }
                }
                Ok(self.ctx.i64_type().const_zero().into())
            }

            Expr::If { condition, then_body, elsif_branches, else_body, .. } => {
                self.if_stmt(condition, then_body, elsif_branches, else_body)?;
                Ok(self.ctx.i64_type().const_zero().into())
            }

            Expr::While { condition, body, .. } => {
                self.while_stmt(condition, body)?;
                Ok(self.ctx.i64_type().const_zero().into())
            }

            Expr::For { pattern, iterable, body, .. } => {
                self.for_stmt(pattern, iterable, body)?;
                Ok(self.ctx.i64_type().const_zero().into())
            }

            Expr::Cast(inner, ty, _) => {
                let v   = self.expr(inner, None)?;
                let dst = htype_to_llvm(self.ctx, ty).unwrap_or(self.ctx.i64_type().into());
                self.cast(v, dst)
            }

            Expr::Return(val, _) => {
                if let Some(expr) = val {
                    let v = self.expr(expr, None)?;
                    let v = self.coerce_ret(v);
                    self.builder.build_return(Some(&v)).unwrap();
                } else if self.fn_name == "main" {
                    let z = self.ctx.i32_type().const_int(0, false);
                    self.builder.build_return(Some(&z)).unwrap();
                } else {
                    self.builder.build_return(None).unwrap();
                }
                Ok(self.ctx.i64_type().const_zero().into())
            }

            Expr::Range(start, _, _, _) => self.expr(start, hint),
            _ => Ok(self.ctx.i64_type().const_zero().into()),
        }
    }

    fn literal(&mut self, lit: &Literal, hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
        Ok(match lit {
            Literal::Int(n) => {
                let t = match hint {
                    Some(BasicTypeEnum::IntType(t)) => t,
                    _ => self.ctx.i64_type(),
                };
                t.const_int(*n as u64, true).into()
            }
            Literal::Float(f) => {
                let t = match hint {
                    Some(BasicTypeEnum::FloatType(t)) => t,
                    _ => self.ctx.f64_type(),
                };
                t.const_float(*f).into()
            }
            Literal::Bool(b)  => self.ctx.i8_type().const_int(if *b { 1 } else { 0 }, false).into(),
            Literal::Nil      => self.ctx.i64_type().const_zero().into(),
            Literal::String(s) => {
                let ptr = if let Some(&g) = self.str_globals.get(s.as_str()) {
                    g
                } else {
                    let gs = self.builder.build_global_string_ptr(s, ".str").unwrap();
                    let p = gs.as_pointer_value();
                    self.str_globals.insert(s.clone(), p);
                    p
                };
                ptr.into()
            }
            Literal::Bytes(_) => self.ctx.i64_type().const_zero().into(),
        })
    }

    fn call_fn(&mut self, name: &str, args: &[Expr], hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
        let i8ptr = self.ctx.i8_type().ptr_type(AddressSpace::default());

        macro_rules! str_arg {
            ($i:expr) => {
                if let Some(a) = args.get($i) {
                    self.expr(a, Some(i8ptr.into()))?
                } else {
                    let g = self.builder.build_global_string_ptr("", ".empty").unwrap();
                    g.as_pointer_value().into()
                }
            }
        }

        match name {
            "println" | "write" | "writeln" => {
                let a = str_arg!(0);
                self.builder.build_call(self.builtins.hsh_println, &[a.into()], "").unwrap();
                Ok(self.ctx.i64_type().const_zero().into())
            }
            "print" => {
                let a = str_arg!(0);
                self.builder.build_call(self.builtins.hsh_print, &[a.into()], "").unwrap();
                Ok(self.ctx.i64_type().const_zero().into())
            }
            "to_string" => {
                let a = if let Some(e) = args.first() {
                    self.expr(e, Some(self.ctx.i64_type().into()))?
                } else { self.ctx.i64_type().const_zero().into() };
                let r = self.builder.build_call(self.builtins.hsh_int_to_string, &[a.into()], "ts").unwrap();
                Ok(r.try_as_basic_value().left().unwrap())
            }
            "len" => {
                let a = str_arg!(0);
                let r = self.builder.build_call(self.builtins.hsh_strlen, &[a.into()], "len").unwrap();
                Ok(r.try_as_basic_value().left().unwrap())
            }
            "panic" => {
                let a = str_arg!(0);
                self.builder.build_call(self.builtins.hsh_panic, &[a.into()], "").unwrap();
                self.builder.build_unreachable().unwrap();
                Ok(self.ctx.i64_type().const_zero().into())
            }
            "exit" => {
                let code = if let Some(e) = args.first() {
                    let v = self.expr(e, Some(self.ctx.i32_type().into()))?;
                    match v { BasicValueEnum::IntValue(i) => i.into(), _ => self.ctx.i32_type().const_zero().into() }
                } else { self.ctx.i32_type().const_zero().into() };
                self.builder.build_call(self.builtins.exit_fn, &[code], "").unwrap();
                self.builder.build_unreachable().unwrap();
                Ok(self.ctx.i64_type().const_zero().into())
            }
            _ => {
                // User function
                if let Some(&fv) = self.func_vals.get(name) {
                    let sig = fv.get_type();
                    let mut call_args = Vec::new();
                    for (i, a) in args.iter().enumerate() {
                        let expected = sig.get_param_types().get(i).copied().map(|t| t);
                        let v = self.expr(a, None)?;
                        call_args.push(v.into());
                    }
                    let r = self.builder.build_call(fv, &call_args, "call").unwrap();
                    Ok(r.try_as_basic_value().left()
                        .unwrap_or(self.ctx.i64_type().const_zero().into()))
                } else {
                    Ok(self.ctx.i64_type().const_zero().into())
                }
            }
        }
    }

    fn binop(&mut self, op: &BinOp, lv: BasicValueEnum<'ctx>, rv: BasicValueEnum<'ctx>) -> R<BasicValueEnum<'ctx>> {
        // String concatenation for Add on pointer types
        if matches!(op, BinOp::Add) {
            if let (BasicValueEnum::PointerValue(_), BasicValueEnum::PointerValue(_)) = (&lv, &rv) {
                let r = self.builder.build_call(
                    self.builtins.hsh_strcat, &[lv.into(), rv.into()], "cat"
                ).unwrap();
                return Ok(r.try_as_basic_value().left().unwrap());
            }
        }

        Ok(match (lv, rv) {
            (BasicValueEnum::IntValue(l), BasicValueEnum::IntValue(r)) => {
                match op {
                    BinOp::Add    => self.builder.build_int_add(l, r, "add").unwrap().into(),
                    BinOp::Sub    => self.builder.build_int_sub(l, r, "sub").unwrap().into(),
                    BinOp::Mul    => self.builder.build_int_mul(l, r, "mul").unwrap().into(),
                    BinOp::Div    => self.builder.build_int_signed_div(l, r, "div").unwrap().into(),
                    BinOp::Mod    => self.builder.build_int_signed_rem(l, r, "rem").unwrap().into(),
                    BinOp::BitAnd => self.builder.build_and(l, r, "and").unwrap().into(),
                    BinOp::BitOr  => self.builder.build_or(l, r, "or").unwrap().into(),
                    BinOp::BitXor => self.builder.build_xor(l, r, "xor").unwrap().into(),
                    BinOp::Shl    => self.builder.build_left_shift(l, r, "shl").unwrap().into(),
                    BinOp::Shr    => self.builder.build_right_shift(l, r, true, "shr").unwrap().into(),
                    BinOp::Eq    => self.builder.build_int_compare(inkwell::IntPredicate::EQ,  l, r, "eq").unwrap().into(),
                    BinOp::NotEq  => self.builder.build_int_compare(inkwell::IntPredicate::NE,  l, r, "ne").unwrap().into(),
                    BinOp::Lt    => self.builder.build_int_compare(inkwell::IntPredicate::SLT, l, r, "lt").unwrap().into(),
                    BinOp::Gt    => self.builder.build_int_compare(inkwell::IntPredicate::SGT, l, r, "gt").unwrap().into(),
                    BinOp::LtEq  => self.builder.build_int_compare(inkwell::IntPredicate::SLE, l, r, "le").unwrap().into(),
                    BinOp::GtEq  => self.builder.build_int_compare(inkwell::IntPredicate::SGE, l, r, "ge").unwrap().into(),
                    BinOp::And   => self.builder.build_and(l, r, "land").unwrap().into(),
                    BinOp::Or    => self.builder.build_or(l, r, "lor").unwrap().into(),
                }
            }
            (BasicValueEnum::FloatValue(l), BasicValueEnum::FloatValue(r)) => {
                match op {
                    BinOp::Add  => self.builder.build_float_add(l, r, "fadd").unwrap().into(),
                    BinOp::Sub  => self.builder.build_float_sub(l, r, "fsub").unwrap().into(),
                    BinOp::Mul  => self.builder.build_float_mul(l, r, "fmul").unwrap().into(),
                    BinOp::Div  => self.builder.build_float_div(l, r, "fdiv").unwrap().into(),
                    BinOp::Eq   => self.builder.build_float_compare(inkwell::FloatPredicate::OEQ, l, r, "feq").unwrap().into(),
                    BinOp::Lt   => self.builder.build_float_compare(inkwell::FloatPredicate::OLT, l, r, "flt").unwrap().into(),
                    BinOp::Gt   => self.builder.build_float_compare(inkwell::FloatPredicate::OGT, l, r, "fgt").unwrap().into(),
                    _ => self.ctx.f64_type().const_zero().into(),
                }
            }
            _ => self.ctx.i64_type().const_zero().into(),
        })
    }

    fn cast(&mut self, v: BasicValueEnum<'ctx>, dst: BasicTypeEnum<'ctx>) -> R<BasicValueEnum<'ctx>> {
        Ok(match (v, dst) {
            (BasicValueEnum::IntValue(i), BasicTypeEnum::IntType(t)) => {
                if i.get_type().get_bit_width() > t.get_bit_width() {
                    self.builder.build_int_truncate(i, t, "trunc").unwrap().into()
                } else {
                    self.builder.build_int_s_extend(i, t, "sext").unwrap().into()
                }
            }
            (BasicValueEnum::IntValue(i), BasicTypeEnum::FloatType(t)) =>
                self.builder.build_signed_int_to_float(i, t, "i2f").unwrap().into(),
            (BasicValueEnum::FloatValue(f), BasicTypeEnum::IntType(t)) =>
                self.builder.build_float_to_signed_int(f, t, "f2i").unwrap().into(),
            (BasicValueEnum::FloatValue(f), BasicTypeEnum::FloatType(t)) =>
                if f.get_type() == self.ctx.f64_type() && t != self.ctx.f64_type() {
                    self.builder.build_float_trunc(f, t, "ftrunc").unwrap().into()
                } else if f.get_type() != self.ctx.f64_type() && t == self.ctx.f64_type() {
                    self.builder.build_float_ext(f, t, "fext").unwrap().into()
                } else { f.into() },
            _ => v,
        })
    }

    fn as_bool(&mut self, e: &Expr) -> R<inkwell::values::IntValue<'ctx>> {
        let v = self.expr(e, Some(self.ctx.i8_type().into()))?;
        match v {
            BasicValueEnum::IntValue(i) => {
                let z = i.get_type().const_zero();
                Ok(self.builder.build_int_compare(inkwell::IntPredicate::NE, i, z, "bool").unwrap())
            }
            BasicValueEnum::FloatValue(f) => {
                let z = f.get_type().const_float(0.0);
                Ok(self.builder.build_float_compare(inkwell::FloatPredicate::ONE, f, z, "fbool").unwrap())
            }
            _ => Ok(self.ctx.i8_type().const_int(1, false)),
        }
    }

    fn coerce_ret(&mut self, v: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
        if self.fn_name != "main" { return v; }
        let i32t = self.ctx.i32_type();
        match v {
            BasicValueEnum::IntValue(i) if i.get_type() != i32t => {
                self.builder.build_int_cast(i, i32t, "ret_cast").unwrap().into()
            }
            _ => v,
        }
    }

    fn zero(&self, ty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match ty {
            BasicTypeEnum::IntType(t)     => t.const_zero().into(),
            BasicTypeEnum::FloatType(t)   => t.const_zero().into(),
            BasicTypeEnum::PointerType(t) => t.const_null().into(),
            _ => self.ctx.i64_type().const_zero().into(),
        }
    }
}
