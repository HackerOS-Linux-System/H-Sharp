use cranelift::prelude::*;
use cranelift_codegen::ir::{AbiParam, Function, Signature, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_module::{DataDescription, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use hsharp_parser::ast::*;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CodegenError {
    #[error("Cranelift error: {0}")]
    Cranelift(String),
    #[error("Module error: {0}")]
    Module(#[from] cranelift_module::ModuleError),
    #[error("Niezaimplementowana funkcja: {0}")]
    Unimplemented(String),
    #[error("Nieznany typ: {0}")]
    UnknownType(String),
    #[error("Anyhow: {0}")]
    Anyhow(#[from] anyhow::Error),
}

/// Mapowanie nazw lokalnych zmiennych -> Value
type Locals = HashMap<String, Value>;

/// Główny kod generatora
pub struct Codegen {
    module: ObjectModule,
    string_data: HashMap<String, cranelift_module::DataId>,
}

impl Codegen {
    pub fn new(triple: target_lexicon::Triple) -> Result<Self, CodegenError> {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false")
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?;
        flag_builder.set("is_pic", "false")
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?;
        flag_builder.set("opt_level", "speed")
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?;

        let flags = settings::Flags::new(flag_builder);
        let isa = cranelift_codegen::isa::lookup(triple)
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?
        .finish(flags)
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?;

        let builder = ObjectBuilder::new(
            isa,
            "hsharp_module",
            cranelift_module::default_libcall_names(),
        )?;

        let module = ObjectModule::new(builder);

        Ok(Self {
            module,
            string_data: HashMap::new(),
        })
    }

    /// Generuje kod dla całego modułu H#
    pub fn compile_module(&mut self, module: &HsharpModule) -> Result<Vec<u8>, CodegenError> {
        // Najpierw deklarujemy zewnętrzne funkcje (printf, malloc, free itp.)
        self.declare_runtime()?;

        // Kompilujemy każdą funkcję
        for decl in &module.decls {
            match decl {
                Decl::Function { name, params, return_ty, body, .. } => {
                    self.compile_function(name, params, return_ty, body)?;
                }
                _ => {} // Inne deklaracje (klasy, enumy) - TODO
            }
        }

        // Finalizujemy i zwracamy obiektowy plik binarny
        let product = self.module.finish();
        product.emit()
        .map_err(|e| CodegenError::Cranelift(e.to_string()))
    }

    fn declare_runtime(&mut self) -> Result<(), CodegenError> {
        // printf(const char*, ...) -> int
        let mut printf_sig = self.module.make_signature();
        printf_sig.params.push(AbiParam::new(types::I64)); // char*
        printf_sig.returns.push(AbiParam::new(types::I32));
        self.module.declare_function("printf", Linkage::Import, &printf_sig)?;

        // malloc(size_t) -> void*
        let mut malloc_sig = self.module.make_signature();
        malloc_sig.params.push(AbiParam::new(types::I64));
        malloc_sig.returns.push(AbiParam::new(types::I64));
        self.module.declare_function("malloc", Linkage::Import, &malloc_sig)?;

        // free(void*)
        let mut free_sig = self.module.make_signature();
        free_sig.params.push(AbiParam::new(types::I64));
        self.module.declare_function("free", Linkage::Import, &free_sig)?;

        // exit(int)
        let mut exit_sig = self.module.make_signature();
        exit_sig.params.push(AbiParam::new(types::I32));
        self.module.declare_function("exit", Linkage::Import, &exit_sig)?;

        Ok(())
    }

    fn compile_function(
        &mut self,
        name: &str,
        params: &[Param],
        return_ty: &Ty,
        body: &[Stmt],
    ) -> Result<(), CodegenError> {
        let mut sig = self.module.make_signature();

        // Parametry
        for param in params {
            sig.params.push(AbiParam::new(self.ty_to_cranelift(&param.ty)?));
        }

        // Typ powrotu
        if !matches!(return_ty, Ty::Void) {
            sig.returns.push(AbiParam::new(self.ty_to_cranelift(return_ty)?));
        }

        // Linkage: main jest Export, reszta Local
        let linkage = if name == "main" || name == "glowna" {
            Linkage::Export
        } else {
            Linkage::Export
        };

        let func_id = self.module.declare_function(name, linkage, &sig)?;

        let mut ctx = self.module.make_context();
        ctx.func.signature = sig.clone();
        ctx.func.name = UserFuncName::user(0, func_id.as_u32());

        {
            let mut func_ctx = FunctionBuilderContext::new();
            let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);

            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);
            builder.seal_block(entry_block);

            // Wczytaj parametry
            let mut locals: Locals = HashMap::new();
            for (i, param) in params.iter().enumerate() {
                let val = builder.block_params(entry_block)[i];
                locals.insert(param.name.clone(), val);
            }

            let mut fg = FuncGen {
                builder: &mut builder,
                module: &mut self.module,
                locals,
                string_data: &mut self.string_data,
                return_ty: return_ty.clone(),
            };

            fg.compile_body(body)?;

            // Jeśli brak explicit return, dodaj domyślny
            if !fg.builder.is_filled() {
                if matches!(return_ty, Ty::Void) {
                    fg.builder.ins().return_(&[]);
                } else {
                    let zero = fg.builder.ins().iconst(types::I64, 0);
                    fg.builder.ins().return_(&[zero]);
                }
            }

            builder.finalize();
        }

        self.module
        .define_function(func_id, &mut ctx)
        .map_err(|e| CodegenError::Cranelift(e.to_string()))?;

        self.module.clear_context(&mut ctx);

        Ok(())
    }

    fn ty_to_cranelift(&self, ty: &Ty) -> Result<Type, CodegenError> {
        match ty {
            Ty::Int => Ok(types::I64),
            Ty::Float => Ok(types::F64),
            Ty::Bool => Ok(types::I8),
            Ty::Char => Ok(types::I32),
            Ty::Str => Ok(types::I64),  // wskaźnik
            Ty::Arc(_) | Ty::Box(_) => Ok(types::I64),  // wskaźnik
            Ty::Named(_) | Ty::Generic(_, _) => Ok(types::I64), // wskaźnik do heapa
            Ty::List(_) | Ty::Map(_, _) => Ok(types::I64), // wskaźnik
            Ty::Option(_) => Ok(types::I64),
            Ty::Result(_, _) => Ok(types::I64),
            Ty::Infer => Ok(types::I64),
            Ty::Void => Err(CodegenError::UnknownType("Void nie ma reprezentacji".to_string())),
            other => Err(CodegenError::UnknownType(format!("{}", other))),
        }
    }
}

/// Generator kodu dla pojedynczej funkcji
struct FuncGen<'a> {
    builder: &'a mut FunctionBuilder<'a>,
    module: &'a mut ObjectModule,
    locals: Locals,
    string_data: &'a mut HashMap<String, cranelift_module::DataId>,
    return_ty: Ty,
}

impl<'a> FuncGen<'a> {
    fn compile_body(&mut self, stmts: &[Stmt]) -> Result<(), CodegenError> {
        for stmt in stmts {
            self.compile_stmt(stmt)?;
            if self.builder.is_filled() {
                break; // Już zakończono blok (np. return)
            }
        }
        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt) -> Result<(), CodegenError> {
        match stmt {
            Stmt::Let { name, value, .. } => {
                if let Some(val_expr) = value {
                    let val = self.compile_expr(val_expr)?;
                    self.locals.insert(name.clone(), val);
                }
            }
            Stmt::Expr(e) => {
                self.compile_expr(e)?;
            }
            Stmt::Return(val) => {
                if let Some(v) = val {
                    let ret_val = self.compile_expr(v)?;
                    self.builder.ins().return_(&[ret_val]);
                } else {
                    self.builder.ins().return_(&[]);
                }
            }
            Stmt::Assign { target, value, .. } => {
                let val = self.compile_expr(value)?;
                if let Expr::Var(name) = target.as_ref() {
                    self.locals.insert(name.clone(), val);
                }
            }
            Stmt::While { cond, body, .. } => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.builder.ins().jump(header_block, &[]);
                self.builder.switch_to_block(header_block);

                let cond_val = self.compile_expr(cond)?;
                self.builder.ins().brif(cond_val, body_block, &[], exit_block, &[]);

                self.builder.switch_to_block(body_block);
                self.compile_body(body)?;
                if !self.builder.is_filled() {
                    self.builder.ins().jump(header_block, &[]);
                }

                self.builder.seal_block(body_block);
                self.builder.seal_block(header_block);
                self.builder.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);
            }
            Stmt::For { var, iterable, body, span } => {
                // Uproszczona implementacja for: obsługujemy zakres Int
                // TODO: pełna iteracja po listach
                let iter_val = self.compile_expr(iterable)?;
                // Na razie traktujemy jako pętlę po liczbach 0..n
                let zero = self.builder.ins().iconst(types::I64, 0);
                let counter = self.builder.ins().iconst(types::I64, 0);

                let header = self.builder.create_block();
                let body_b = self.builder.create_block();
                let exit_b = self.builder.create_block();

                self.builder.append_block_param(header, types::I64);
                self.builder.ins().jump(header, &[zero]);
                self.builder.switch_to_block(header);

                let i = self.builder.block_params(header)[0];
                self.locals.insert(var.clone(), i);

                let cond = self.builder.ins().icmp(IntCC::SignedLessThan, i, iter_val);
                self.builder.ins().brif(cond, body_b, &[], exit_b, &[]);

                self.builder.switch_to_block(body_b);
                self.compile_body(body)?;
                if !self.builder.is_filled() {
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let next_i = self.builder.ins().iadd(i, one);
                    self.builder.ins().jump(header, &[next_i]);
                }

                self.builder.seal_block(body_b);
                self.builder.seal_block(header);
                self.builder.switch_to_block(exit_b);
                self.builder.seal_block(exit_b);
            }
            _ => {
                // Inne instrukcje - TODO
            }
        }
        Ok(())
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<Value, CodegenError> {
        match expr {
            Expr::Int(n) => Ok(self.builder.ins().iconst(types::I64, *n)),
            Expr::Float(f) => Ok(self.builder.ins().f64const(*f)),
            Expr::Bool(b) => Ok(self.builder.ins().iconst(types::I8, if *b { 1 } else { 0 })),
            Expr::Char(c) => Ok(self.builder.ins().iconst(types::I32, *c as i64)),
            Expr::Nil => Ok(self.builder.ins().iconst(types::I64, 0)),

            Expr::Str(s) => self.compile_string_literal(s),

            Expr::Var(name) => {
                if let Some(&val) = self.locals.get(name) {
                    Ok(val)
                } else {
                    Err(CodegenError::Cranelift(format!("Niezdefiniowana zmienna: {}", name)))
                }
            }

            Expr::BinOp { op, lhs, rhs, .. } => {
                let l = self.compile_expr(lhs)?;
                let r = self.compile_expr(rhs)?;
                Ok(self.compile_binop(op, l, r))
            }

            Expr::UnaryOp { op, expr, .. } => {
                let val = self.compile_expr(expr)?;
                match op {
                    UnaryOp::Neg => Ok(self.builder.ins().ineg(val)),
                    UnaryOp::Not => {
                        let one = self.builder.ins().iconst(types::I8, 1);
                        Ok(self.builder.ins().bxor(val, one))
                    }
                    UnaryOp::BitNot => Ok(self.builder.ins().bnot(val)),
                }
            }

            Expr::Write { args, newline, .. } => {
                self.compile_write(args, *newline)
            }

            Expr::Block(stmts) => {
                let mut last = self.builder.ins().iconst(types::I64, 0);
                for (i, stmt) in stmts.iter().enumerate() {
                    if i == stmts.len() - 1 {
                        if let Stmt::Expr(e) = stmt {
                            last = self.compile_expr(e)?;
                        } else {
                            self.compile_stmt(stmt)?;
                        }
                    } else {
                        self.compile_stmt(stmt)?;
                    }
                }
                Ok(last)
            }

            Expr::If { cond, then, otherwise, .. } => {
                let cond_val = self.compile_expr(cond)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                self.builder.append_block_param(merge_block, types::I64);

                self.builder.ins().brif(cond_val, then_block, &[], else_block, &[]);

                // Then
                self.builder.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                let then_val = self.compile_expr(then)?;
                if !self.builder.is_filled() {
                    self.builder.ins().jump(merge_block, &[then_val]);
                }

                // Else
                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let else_val = if let Some(e) = otherwise {
                    self.compile_expr(e)?
                } else {
                    self.builder.ins().iconst(types::I64, 0)
                };
                if !self.builder.is_filled() {
                    self.builder.ins().jump(merge_block, &[else_val]);
                }

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
                Ok(self.builder.block_params(merge_block)[0])
            }

            Expr::Call { callee, args, .. } => {
                if let Expr::Var(fname) = callee.as_ref() {
                    return self.compile_call(fname, args);
                }
                Err(CodegenError::Unimplemented("Wywołanie dynamiczne".to_string()))
            }

            Expr::ArcNew(inner) => {
                // Arc::new(x) - alokujemy na heapie i zwracamy wskaźnik
                let val = self.compile_expr(inner)?;
                let size = self.builder.ins().iconst(types::I64, 8);
                let ptr = self.call_malloc(size)?;
                self.builder.ins().store(MemFlags::new(), val, ptr, 0);
                Ok(ptr)
            }

            Expr::Cast { expr, ty, .. } => {
                let val = self.compile_expr(expr)?;
                match ty {
                    Ty::Int => Ok(self.builder.ins().ireduce(types::I64, val)),
                    Ty::Float => Ok(self.builder.ins().fcvt_from_sint(types::F64, val)),
                    _ => Ok(val),
                }
            }

            _ => {
                // Placeholder dla nieimplementowanych wyrażeń
                Ok(self.builder.ins().iconst(types::I64, 0))
            }
        }
    }

    fn compile_binop(&mut self, op: &BinOp, l: Value, r: Value) -> Value {
        match op {
            BinOp::Add => self.builder.ins().iadd(l, r),
            BinOp::Sub => self.builder.ins().isub(l, r),
            BinOp::Mul => self.builder.ins().imul(l, r),
            BinOp::Div => self.builder.ins().sdiv(l, r),
            BinOp::Mod => self.builder.ins().srem(l, r),
            BinOp::Eq => {
                let b = self.builder.ins().icmp(IntCC::Equal, l, r);
                self.builder.ins().uextend(types::I64, b)
            }
            BinOp::NotEq => {
                let b = self.builder.ins().icmp(IntCC::NotEqual, l, r);
                self.builder.ins().uextend(types::I64, b)
            }
            BinOp::Lt => {
                let b = self.builder.ins().icmp(IntCC::SignedLessThan, l, r);
                self.builder.ins().uextend(types::I64, b)
            }
            BinOp::Gt => {
                let b = self.builder.ins().icmp(IntCC::SignedGreaterThan, l, r);
                self.builder.ins().uextend(types::I64, b)
            }
            BinOp::LtEq => {
                let b = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, l, r);
                self.builder.ins().uextend(types::I64, b)
            }
            BinOp::GtEq => {
                let b = self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, l, r);
                self.builder.ins().uextend(types::I64, b)
            }
            BinOp::And => self.builder.ins().band(l, r),
            BinOp::Or => self.builder.ins().bor(l, r),
            BinOp::BitAnd => self.builder.ins().band(l, r),
            BinOp::BitOr => self.builder.ins().bor(l, r),
            BinOp::BitXor => self.builder.ins().bxor(l, r),
            BinOp::LShift => self.builder.ins().ishl(l, r),
            BinOp::RShift => self.builder.ins().sshr(l, r),
            BinOp::Pow => {
                // Uproszczone: x^n przez mnożenie (tylko int)
                // TODO: użyj powi dla float
                l // placeholder
            }
            _ => l, // Assign itp. obsługiwane wyżej
        }
    }

    fn compile_write(&mut self, args: &[Expr], newline: bool) -> Result<Value, CodegenError> {
        // Wywołujemy printf z formatem
        // Uproszczone: obsługujemy jeden argument Int lub Str
        let fmt = if newline { "%s\n\0" } else { "%s\0" };
        let fmt_ptr = self.compile_string_literal(&fmt[..fmt.len()-1])?;

        if args.is_empty() {
            let printf_id = self.module.declare_function(
                "printf",
                Linkage::Import,
                &{
                    let mut s = self.module.make_signature();
                    s.params.push(AbiParam::new(types::I64));
                    s.returns.push(AbiParam::new(types::I32));
                    s
                }
            ).map_err(CodegenError::Module)?;

            let func_ref = self.module.declare_func_in_func(printf_id, self.builder.func);
            self.builder.ins().call(func_ref, &[fmt_ptr]);
        } else {
            let arg_val = self.compile_expr(&args[0])?;
            let printf_id = self.module.declare_function(
                "printf",
                Linkage::Import,
                &{
                    let mut s = self.module.make_signature();
                    s.params.push(AbiParam::new(types::I64));
                    s.params.push(AbiParam::new(types::I64));
                    s.returns.push(AbiParam::new(types::I32));
                    s
                }
            ).map_err(CodegenError::Module)?;

            let func_ref = self.module.declare_func_in_func(printf_id, self.builder.func);
            self.builder.ins().call(func_ref, &[fmt_ptr, arg_val]);
        }

        Ok(self.builder.ins().iconst(types::I64, 0))
    }

    fn compile_call(&mut self, name: &str, args: &[Expr]) -> Result<Value, CodegenError> {
        // Budujemy sygnaturę w locie (uproszczona - wszystko I64)
        let mut sig = self.module.make_signature();
        for _ in args {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = self.module
        .declare_function(name, Linkage::Import, &sig)
        .map_err(CodegenError::Module)?;

        let func_ref = self.module.declare_func_in_func(func_id, self.builder.func);

        let mut arg_vals = Vec::new();
        for arg in args {
            arg_vals.push(self.compile_expr(arg)?);
        }

        let call = self.builder.ins().call(func_ref, &arg_vals);
        let results = self.builder.inst_results(call);
        if results.is_empty() {
            Ok(self.builder.ins().iconst(types::I64, 0))
        } else {
            Ok(results[0])
        }
    }

    fn compile_string_literal(&mut self, s: &str) -> Result<Value, CodegenError> {
        let key = format!("{}\0", s);
        let data_id = if let Some(&id) = self.string_data.get(&key) {
            id
        } else {
            let mut desc = DataDescription::new();
            desc.define(key.as_bytes().to_vec().into_boxed_slice());
            let id = self.module.declare_anonymous_data(false, false)
            .map_err(CodegenError::Module)?;
            self.module.define_data(id, &desc).map_err(CodegenError::Module)?;
            self.string_data.insert(key, id);
            id
        };

        let global = self.module.declare_data_in_func(data_id, self.builder.func);
        Ok(self.builder.ins().global_value(types::I64, global))
    }

    fn call_malloc(&mut self, size: Value) -> Result<Value, CodegenError> {
        let mut sig = self.module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));

        let malloc_id = self.module
        .declare_function("malloc", Linkage::Import, &sig)
        .map_err(CodegenError::Module)?;

        let func_ref = self.module.declare_func_in_func(malloc_id, self.builder.func);
        let call = self.builder.ins().call(func_ref, &[size]);
        Ok(self.builder.inst_results(call)[0])
    }
}

// Alias dla modułu AST
type HsharpModule = hsharp_parser::ast::Module;
