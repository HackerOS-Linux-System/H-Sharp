use anyhow::{Context, Result};
use cranelift::prelude::*;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;

use crate::ast::*;

// --- Module Context ---
pub struct ModuleContext {
    pub module: ObjectModule,
    pub data_ctx: DataDescription,
    pub str_literals: HashMap<String, DataId>,
}

impl ModuleContext {
    pub fn new() -> Result<Self> {
        let flag_builder = settings::builder();
        // Use native target, essentially making it independent of any specific GCC cross-compilation config
        let isa_builder = cranelift_native::builder().map_err(|e| anyhow::anyhow!(e))?;
        let isa = isa_builder.finish(settings::Flags::new(flag_builder))?;

        let builder = ObjectBuilder::new(isa, "h_sharp_program", cranelift_module::default_libcall_names())?;
        let module = ObjectModule::new(builder);

        Ok(Self {
            module,
            data_ctx: DataDescription::new(),
           str_literals: HashMap::new(),
        })
    }

    pub fn get_string_data_id(&mut self, s: &str) -> Result<DataId> {
        if let Some(id) = self.str_literals.get(s) {
            return Ok(*id);
        }
        let mut content = s.as_bytes().to_vec();
        content.push(0);
        self.data_ctx.define(content.into_boxed_slice());
        let id = self.module.declare_data(
            &format!("str_{}", self.str_literals.len()),
                                          Linkage::Local,
                                          true,
                                          false,
        )?;
        self.module.define_data(id, &self.data_ctx)?;
        self.data_ctx.clear();
        self.str_literals.insert(s.to_string(), id);
        Ok(id)
    }
}

// --- Function Compilation ---

struct FunctionTranslator<'a> {
    builder: FunctionBuilder<'a>,
    vars: HashMap<String, Variable>,
    module_ctx: &'a mut ModuleContext,
    ptr_type: Type,
}

impl<'a> FunctionTranslator<'a> {
    fn new(builder: FunctionBuilder<'a>, module_ctx: &'a mut ModuleContext) -> Self {
        let ptr_type = module_ctx.module.target_config().pointer_type();
        Self {
            builder,
            vars: HashMap::new(),
            module_ctx,
            ptr_type,
        }
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<Value> {
        match expr {
            Expr::Literal { type_name, value } => match type_name.as_str() {
                "i32" => Ok(self.builder.ins().iconst(self.ptr_type, value.as_i64().unwrap_or(0))),
                "str" => {
                    let s = value.as_str().unwrap_or("");
                    let data_id = self.module_ctx.get_string_data_id(s)?;
                    let sym = self.module_ctx.module.declare_data_in_func(data_id, self.builder.func);
                    Ok(self.builder.ins().global_value(self.ptr_type, sym))
                },
                "ptr" => Ok(self.builder.ins().iconst(self.ptr_type, 0)),
                _ => Err(anyhow::anyhow!("Unknown literal type")),
            },
            Expr::Var { name } => {
                if let Some(var) = self.vars.get(name) {
                    Ok(self.builder.use_var(*var))
                } else {
                    Err(anyhow::anyhow!("Undefined variable: {}", name))
                }
            },
            Expr::BinaryOp { op, left, right } => {
                let l = self.compile_expr(left)?;
                let r = self.compile_expr(right)?;
                match op.as_str() {
                    "==" => Ok(self.builder.ins().icmp(IntCC::Equal, l, r)),
                    "!=" => Ok(self.builder.ins().icmp(IntCC::NotEqual, l, r)),
                    ">" => Ok(self.builder.ins().icmp(IntCC::SignedGreaterThan, l, r)),
                    "<" => Ok(self.builder.ins().icmp(IntCC::SignedLessThan, l, r)),
                    ">=" => Ok(self.builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, l, r)),
                    "<=" => Ok(self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, l, r)),
                    "+" => Ok(self.builder.ins().iadd(l, r)),
                    "-" => Ok(self.builder.ins().isub(l, r)),
                    _ => Err(anyhow::anyhow!("Unknown binary op: {}", op)),
                }
            },
            Expr::Call { target, args } => {
                let mut arg_vals = Vec::new();
                for arg in args {
                    arg_vals.push(self.compile_expr(arg)?);
                }

                let mut sig = self.module_ctx.module.make_signature();
                for _ in &arg_vals {
                    sig.params.push(AbiParam::new(self.ptr_type));
                }
                sig.returns.push(AbiParam::new(self.ptr_type));

                let func_id = self.module_ctx.module.declare_function(target, Linkage::Import, &sig)?;
                let local_func = self.module_ctx.module.declare_func_in_func(func_id, self.builder.func);

                let call = self.builder.ins().call(local_func, &arg_vals);
                let results = self.builder.inst_results(call);
                if !results.is_empty() {
                    Ok(results[0])
                } else {
                    Ok(self.builder.ins().iconst(self.ptr_type, 0))
                }
            },
            Expr::ArrayGet { target, index } => {
                let idx = self.compile_expr(index)?;
                if let Some(var) = self.vars.get(target) {
                    let base = self.builder.use_var(*var);
                    let pointer_size = 8;
                    let offset = self.builder.ins().imul_imm(idx, pointer_size);
                    let addr = self.builder.ins().iadd(base, offset);
                    Ok(self.builder.ins().load(self.ptr_type, MemFlags::new(), addr, 0))
                } else {
                    Err(anyhow::anyhow!("Array var not found: {}", target))
                }
            }
        }
    }

    fn compile_stmt(&mut self, stmt: &Statement) -> Result<()> {
        match stmt {
            Statement::Log { format, args } => {
                let fmt_id = self.module_ctx.get_string_data_id(format)?;
                let fmt_ref = self.module_ctx.module.declare_data_in_func(fmt_id, self.builder.func);
                let fmt_ptr = self.builder.ins().global_value(self.ptr_type, fmt_ref);

                let mut call_args = vec![fmt_ptr];
                for arg_name in args {
                    if let Some(var) = self.vars.get(arg_name) {
                        call_args.push(self.builder.use_var(*var));
                    } else {
                        call_args.push(self.builder.ins().iconst(self.ptr_type, 0));
                    }
                }

                let mut sig = self.module_ctx.module.make_signature();
                sig.params.push(AbiParam::new(self.ptr_type));
                for _ in 0..args.len() {
                    sig.params.push(AbiParam::new(self.ptr_type));
                }
                sig.returns.push(AbiParam::new(types::I32));

                let printf_id = self.module_ctx.module.declare_function("printf", Linkage::Import, &sig)?;
                let printf_func = self.module_ctx.module.declare_func_in_func(printf_id, self.builder.func);

                self.builder.ins().call(printf_func, &call_args);
            },
            Statement::System { command, args } => {
                if args.is_empty() {
                    let cmd_id = self.module_ctx.get_string_data_id(command)?;
                    let cmd_ref = self.module_ctx.module.declare_data_in_func(cmd_id, self.builder.func);
                    let cmd_ptr = self.builder.ins().global_value(self.ptr_type, cmd_ref);

                    let mut sig = self.module_ctx.module.make_signature();
                    sig.params.push(AbiParam::new(self.ptr_type));
                    sig.returns.push(AbiParam::new(types::I32));

                    let sys_id = self.module_ctx.module.declare_function("system", Linkage::Import, &sig)?;
                    let sys_func = self.module_ctx.module.declare_func_in_func(sys_id, self.builder.func);
                    self.builder.ins().call(sys_func, &[cmd_ptr]);
                } else {
                    let msg = "[Runtime] interpolated system calls not fully implemented in MVP";
                    let msg_id = self.module_ctx.get_string_data_id(msg)?;
                    let msg_ref = self.module_ctx.module.declare_data_in_func(msg_id, self.builder.func);
                    let msg_ptr = self.builder.ins().global_value(self.ptr_type, msg_ref);

                    let mut sig = self.module_ctx.module.make_signature();
                    sig.params.push(AbiParam::new(self.ptr_type));
                    sig.returns.push(AbiParam::new(types::I32));
                    let puts_id = self.module_ctx.module.declare_function("puts", Linkage::Import, &sig)?;
                    let puts_func = self.module_ctx.module.declare_func_in_func(puts_id, self.builder.func);
                    self.builder.ins().call(puts_func, &[msg_ptr]);
                }
            },
            Statement::Let { name, value } => {
                let val = self.compile_expr(value)?;
                let var_idx = self.vars.len();
                let var = Variable::new(var_idx);
                self.builder.declare_var(var, self.ptr_type);
                self.builder.def_var(var, val);
                self.vars.insert(name.clone(), var);
            },
            Statement::Return { value } => {
                let val = self.compile_expr(value)?;
                self.builder.ins().return_(&[val]);
            },
            Statement::If { condition, then, r#else } => {
                let cond_val = self.compile_expr(condition)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.ins().brif(cond_val, then_block, &[], else_block, &[]);

                self.builder.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                for s in then {
                    self.compile_stmt(s)?;
                }
                self.builder.ins().jump(merge_block, &[]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                for s in r#else {
                    self.compile_stmt(s)?;
                }
                self.builder.ins().jump(merge_block, &[]);

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
            },
            Statement::Call { target, args } => {
                self.compile_expr(&Expr::Call { target: target.clone(), args: args.iter().map(|e| match e {
                    Expr::Var { name } => Expr::Var { name: name.clone() },
                                                                                              _ => Expr::Literal { type_name: "i32".into(), value: serde_json::json!(0) }
                }).collect() })?;
            },
            Statement::ArraySet { target, index, value } => {
                let idx = self.compile_expr(index)?;
                let val = self.compile_expr(value)?;

                if let Some(var) = self.vars.get(target) {
                    let base = self.builder.use_var(*var);
                    let pointer_size = 8;
                    let offset = self.builder.ins().imul_imm(idx, pointer_size);
                    let addr = self.builder.ins().iadd(base, offset);
                    self.builder.ins().store(MemFlags::new(), val, addr, 0);
                }
            }
        }
        Ok(())
    }
}

pub fn compile_program(program: Program) -> Result<Vec<u8>> {
    let mut module_ctx = ModuleContext::new()?;
    let mut ctx = module_ctx.module.make_context();
    let mut builder_ctx = FunctionBuilderContext::new();

    for decl in &program.declarations {
        if let Declaration::Function { name, params, body, .. } = decl {
            let is_main = name == "main";
            let ptr_type = module_ctx.module.target_config().pointer_type();

            let mut sig = module_ctx.module.make_signature();
            if is_main {
                sig.params.push(AbiParam::new(types::I32));
                sig.params.push(AbiParam::new(ptr_type));
                sig.returns.push(AbiParam::new(types::I32));
            } else {
                for _ in params {
                    sig.params.push(AbiParam::new(ptr_type));
                }
                sig.returns.push(AbiParam::new(ptr_type));
            }

            let func_id = module_ctx.module.declare_function(name, Linkage::Export, &sig)?;

            ctx.func.signature = sig;

            {
                let mut builder = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
                let entry_block = builder.create_block();
                builder.append_block_params_for_function_params(entry_block);
                builder.switch_to_block(entry_block);
                builder.seal_block(entry_block);

                let mut translator = FunctionTranslator::new(builder, &mut module_ctx);

                for (i, param) in params.iter().enumerate() {
                    let val = translator.builder.block_params(entry_block)[i];
                    let var = Variable::new(i);
                    translator.builder.declare_var(var, ptr_type);
                    translator.builder.def_var(var, val);
                    translator.vars.insert(param.name.clone(), var);
                }

                for stmt in body {
                    translator.compile_stmt(stmt)?;
                }

                if is_main {
                    let zero = translator.builder.ins().iconst(types::I32, 0);
                    translator.builder.ins().return_(&[zero]);
                } else {
                    let zero = translator.builder.ins().iconst(ptr_type, 0);
                    translator.builder.ins().return_(&[zero]);
                }

                translator.builder.finalize();
            }
            module_ctx.module.define_function(func_id, &mut ctx)?;
            module_ctx.module.clear_context(&mut ctx);
        }
    }

    let product = module_ctx.module.finish();
    Ok(product.emit()?)
}
