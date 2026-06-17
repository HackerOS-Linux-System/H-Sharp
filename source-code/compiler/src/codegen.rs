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
use crate::CompileOptions;
use crate::llvm_types::htype_to_llvm;
use crate::builtins::LlvmBuiltins;
use crate::llvm_optimize::{optimize_module, mark_nounwind};
use crate::ffi_linker;

#[derive(Debug, thiserror::Error)]
pub enum CodegenError {
    #[error("LLVM: {0}")]          Llvm(String),
    #[error("undefined var: {0}")] UndefinedVar(String),
    #[error("undefined fn: {0}")]  UndefinedFn(String),
    #[error("io: {0}")]            Io(#[from] std::io::Error),
    #[error("link: {0}")]          Link(String),
}
type R<T> = Result<T, CodegenError>;

pub struct LlvmCodegen {
    context: Context,
    opts:    CompileOptions,
    /// §5: link flags collected from `extern [c/cpp/rust, "library"]` blocks
    /// in the module being compiled. Populated at the start of
    /// `compile_full` (which takes `&self`, hence `RefCell`).
    link_flags: std::cell::RefCell<ffi_linker::LinkFlags>,
}

impl LlvmCodegen {
    pub fn new(opts: &CompileOptions) -> R<Self> {
        Target::initialize_x86(&InitializationConfig::default());
        Ok(Self {
            context: Context::create(),
           opts: opts.clone(),
           link_flags: std::cell::RefCell::new(ffi_linker::LinkFlags::default()),
        })
    }

    pub fn declare_functions(&mut self, _m: &HshModule) -> R<()> { Ok(()) }
    pub fn compile_module(&mut self, _m: &HshModule) -> R<()>    { Ok(()) }
    pub fn get_ir(&self)        -> String { String::new() }
    pub fn emit(&self, _output: &str, _optimize: bool) -> R<()> { Ok(()) }
    pub fn emit_object_file(&self, _out: &str) -> R<()>         { Ok(()) }

    /// Full compilation: AST -> LLVM IR -> optimised binary.
    pub fn compile_full(&self, m: &HshModule) -> R<()> {
        let (module, machine) = self.build_module(m)?;
        self.emit_binary_with_machine(&module, &machine)
    }

    /// Build + optimize the LLVM IR for `m` without emitting a binary, and
    /// return it as text. Used by `h# --emit-ir`.
    pub fn compile_to_ir(&self, m: &HshModule) -> R<String> {
        let (module, _machine) = self.build_module(m)?;
        Ok(module.print_to_string().to_string())
    }

    /// Shared by `compile_full` and `compile_to_ir`: build the LLVM module
    /// (declare + compile all functions, including extern C/C++/Rust/Python
    /// handling) and run the optimization pipeline. Returns the optimized
    /// module plus the target machine used to optimize it (also needed by
    /// `emit_binary_with_machine` for object-file emission).
    fn build_module(&self, m: &HshModule) -> R<(Module<'_>, TargetMachine)> {
        let ctx     = &self.context;
        let module  = ctx.create_module("hsharp_module");
        let builder = ctx.create_builder();
        let builtins = LlvmBuiltins::declare(ctx, &module);

        let mut func_vals:   HashMap<String, FunctionValue>  = HashMap::new();
        let mut str_globals: HashMap<String, PointerValue>   = HashMap::new();

        // ── §5 FFI: extern blocks (C / C++ / Rust / Python) ───────────────
        //
        // `ffi_linker::collect_link_flags` walks every `Item::Extern` and
        // produces the `-l...`/whole-archive flags needed at link time
        // (see ffi_linker.rs for the C/C++/Rust rules). We mirror that same
        // walk here to also DECLARE each extern function in the LLVM
        // module so calls to it resolve at link time.
        *self.link_flags.borrow_mut() = ffi_linker::collect_link_flags(m);

        for item in &m.items {
            if let Item::Extern(ext) = item {
                match ext.lang {
                    ExternLang::C | ExternLang::Cpp | ExternLang::Rust => {
                        // C/C++/Rust externs: declare with Linkage::External.
                        // The actual symbol comes from libc, -l{library}
                        // (C/C++), or a Rust staticlib linked
                        // whole-archive (see ffi_linker.rs) so #[no_mangle]
                        // symbols aren't garbage-collected by the linker
                        // before our call sites reference them.
                        //
                        // C++ caveat (documented in ffi_linker.rs and the
                        // roadmap): this only resolves correctly if the
                        // C++ library exports these symbols with
                        // `extern "C"` linkage (no Itanium mangling). H#
                        // does not implement a C++ name mangler.
                        for fn_decl in &ext.functions {
                            let sig = self.build_extern_fn_type(ctx, fn_decl);
                            let fv = if let Some(existing) = module.get_function(&fn_decl.name) {
                                existing
                            } else {
                                module.add_function(&fn_decl.name, sig, Some(inkwell::module::Linkage::External))
                            };
                            // Register so `call_fn`'s fallback
                            // (`self.func_vals.get(name)`) resolves calls
                            // to this extern symbol exactly like a
                            // user-defined H# function.
                            func_vals.insert(fn_decl.name.clone(), fv);
                        }
                    }
                    ExternLang::Python => {
                        // Phase 1.5: generate a REAL callable trampoline
                        // function for each declared `fn` in this block.
                        // The trampoline marshals H# args into a Python
                        // expression string, evaluates it via
                        // `hsh_py_eval` (subprocess `python3 -c`, no
                        // shell), and marshals the result back to the
                        // declared H# return type.
                        //
                        // `ext.library` is the Python module name, e.g.
                        // `extern [python, "numpy"] is fn mean(data: string) -> f64 ... end`
                        // generates:
                        //   f64 mean(string data) {
                        //     code = "import numpy\nprint(numpy.mean(" + repr(data) + "))"
                        //     out  = trim(py_eval(code))
                        //     return atof(out)
                        //   }
                        let module_name = ext.library.clone().unwrap_or_else(|| "__main__".to_string());
                        for fn_decl in &ext.functions {
                            let sig = self.build_extern_fn_type(ctx, fn_decl);
                            let fv = module.add_function(&fn_decl.name, sig, None);
                            mark_nounwind(fv);
                            self.compile_python_trampoline(
                                ctx, &module, &builder, &builtins, &module_name, fn_decl, fv,
                            )?;
                            func_vals.insert(fn_decl.name.clone(), fv);
                        }
                    }
                }
            }
        }

        // Pass 1: declare signatures for H#-defined functions/methods
        let fns = self.collect_fns(m);
        for f in &fns {
            let sig = self.build_fn_type(ctx, f);
            let fv  = module.add_function(&f.name, sig, None);
            mark_nounwind(fv); // H# has no unwinding (panic = abort/exit) — see llvm_optimize.rs
            func_vals.insert(f.name.clone(), fv);
        }

        // Pass 2: compile bodies
        for f in &fns {
            let fv = func_vals[&f.name];
            self.compile_fn(ctx, &module, &builder, &builtins, f, fv,
                            &func_vals, &mut str_globals)?;
        }

        // Target machine — tuned for the HOST CPU (native -march=native
        // equivalent) so generated binaries use AVX2/BMI2/etc when
        // available, matching the performance goal of this pass.
        Target::initialize_native(&InitializationConfig::default())
        .map_err(CodegenError::Llvm)?;
        let triple  = TargetMachine::get_default_triple();
        let target  = Target::from_triple(&triple)
        .map_err(|e| CodegenError::Llvm(e.to_string()))?;
        let opt_lvl = if self.opts.optimize { OptimizationLevel::Aggressive }
        else                   { OptimizationLevel::Default };

        let cpu_name     = TargetMachine::get_host_cpu_name();
        let cpu_features = TargetMachine::get_host_cpu_features();
        let cpu_str  = cpu_name.to_str().unwrap_or("x86-64");
        let feat_str = cpu_features.to_str().unwrap_or("+avx2,+bmi,+bmi2,+sse4.1,+sse4.2,+popcnt");

        let machine = target.create_target_machine(
            &triple, cpu_str, feat_str,
            opt_lvl, RelocMode::PIC, CodeModel::Small,
        ).ok_or_else(|| CodegenError::Llvm("cannot create target machine".into()))?;

        // ── SEGFAULT FIX (kept) ───────────────────────────────────────────
        // Only ONE optimization call per module. Previously:
        // optimize_module(O3) + minimize_size() caused a double-pipeline
        // segfault in LLVM's pass manager on --release. Single call only;
        // O3 already includes DCE + inlining + vectorization + size opts.
        let opt_num = if self.opts.optimize { 3 } else { 0 };
        optimize_module(&module, &machine, opt_num);
        // minimize_size intentionally removed — do NOT re-add it after O3.
        // ───────────────────────────────────────────────────────────────────

        Ok((module, machine))
    }

    fn collect_fns(&self, m: &HshModule) -> Vec<FnDef> {
        let mut fns = Vec::new();
        for item in &m.items {
            match item {
                Item::FnDef(f) => fns.push(f.clone()),
                Item::ImplBlock(imp) => {
                    for method in &imp.methods {
                        fns.push(FnDef {
                            attrs: vec![], type_params: vec![],
                            name:        format!("{}_{}", imp.type_name, method.name),
                                 params:      method.params.clone(),
                                 return_type: method.return_type.clone(),
                                 body:        method.body.clone(),
                                 pub_:        method.pub_,
                                 is_async:    false,
                                 is_unsafe:   method.is_unsafe,
                                 span:        method.span.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        fns
    }

    fn build_fn_type<'ctx>(&self, ctx: &'ctx Context, f: &FnDef)
    -> inkwell::types::FunctionType<'ctx>
    {
        use inkwell::types::BasicMetadataTypeEnum;
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
            None      => ctx.void_type().fn_type(&param_types, false),
            Some(ret) => match htype_to_llvm(ctx, ret) {
                None    => ctx.void_type().fn_type(&param_types, false),
                Some(t) => t.fn_type(&param_types, false),
            }
        }
    }

    /// §5: build an LLVM function type for an `extern [c/cpp/rust/python,
    /// "lib"] fn name(...)` declaration. Unlike `build_fn_type` (for
    /// H#-defined functions), this:
    ///   - never special-cases `main`
    ///   - honors `ExternFnDecl.variadic` (e.g. C's `printf`-style functions)
    ///   - treats a missing return type as `void` (C convention), not `i64`
    fn build_extern_fn_type<'ctx>(&self, ctx: &'ctx Context, f: &ExternFnDecl)
    -> inkwell::types::FunctionType<'ctx>
    {
        use inkwell::types::BasicMetadataTypeEnum;
        let mut param_types: Vec<BasicMetadataTypeEnum> = Vec::new();
        for p in &f.params {
            if let Some(t) = htype_to_llvm(ctx, &p.ty) {
                param_types.push(t.into());
            }
        }
        match &f.return_type {
            None      => ctx.void_type().fn_type(&param_types, f.variadic),
            Some(ret) => match htype_to_llvm(ctx, ret) {
                None    => ctx.void_type().fn_type(&param_types, f.variadic),
                Some(t) => t.fn_type(&param_types, f.variadic),
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
        let mut pidx = 0u32;
        for p in &f.params {
            if p.name == "self" { continue; }
            if let Some(llvm_ty) = htype_to_llvm(ctx, &p.ty) {
                let param_val = fv.get_nth_param(pidx).unwrap();
                let ptr       = builder.build_alloca(llvm_ty, &p.name).unwrap();
                builder.build_store(ptr, param_val).unwrap();
                vars.insert(p.name.clone(), ptr);
                pidx += 1;

                // Performance: H# string/bytes params are guaranteed
                // non-null by the runtime's `if (!s) return "";` contract
                // (see runtime.rs). Telling LLVM this lets it elide
                // defensive null checks around every use of the param.
                if matches!(llvm_ty, BasicTypeEnum::PointerType(_)) {
                    crate::llvm_optimize::mark_param_nonnull(fv, pidx - 1);
                }
            }
        }

        let mut cx = FnCx {
            ctx, module, builder, builtins, func_vals, str_globals,
            vars, fn_name: f.name.clone(), ret_type: f.return_type.clone(),
        };
        let terminated = cx.stmts(&f.body)?;

        if !terminated {
            if f.name == "main" {
                let z = ctx.i32_type().const_int(0, false);
                builder.build_return(Some(&z)).unwrap();
            } else if f.return_type.is_none() {
                builder.build_return(None).unwrap();
            } else {
                let ct   = f.return_type.as_ref().and_then(|t| htype_to_llvm(ctx, t))
                .unwrap_or(ctx.i64_type().into());
                let zero = self.zero_val(ctx, ct);
                builder.build_return(Some(&zero)).unwrap();
            }
        }
        Ok(())
    }

    fn zero_val<'ctx>(&self, ctx: &'ctx Context, ty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match ty {
            BasicTypeEnum::IntType(t)     => t.const_zero().into(),
            BasicTypeEnum::FloatType(t)   => t.const_zero().into(),
            BasicTypeEnum::PointerType(t) => t.const_null().into(),
            _                             => ctx.i64_type().const_zero().into(),
        }
    }

    /// §5 phase 1.5: generate a callable trampoline body for one
    /// `extern [python, "module"] fn name(params...) -> ret` declaration.
    ///
    /// Generated logic (all via direct IR builder calls — no AST/FnCx
    /// needed, the body shape is fixed):
    ///
    ///   1. Build a Python source string:
    ///        "import {module}\nprint({module}.{name}(<args>))"
    ///      where each H# argument is marshaled to a Python literal:
    ///        - string params -> `hsh_py_repr(arg)`  (proper 'quoted' literal)
    ///        - numeric/bool params -> `hsh_int_to_string(arg)` (valid Python int literal)
    ///   2. Call `hsh_py_eval(code)` -> captured stdout (includes trailing "\n" from `print`)
    ///   3. `hsh_trim(...)` to strip the trailing newline
    ///   4. Marshal the result back to the declared return type:
    ///        - `string` (or no return type) -> the trimmed string as-is
    ///        - numeric types -> `hsh_atoll(trimmed)`
    ///        - `f32`/`f64` -> `hsh_atof(trimmed)`
    ///        - `bool` -> `hsh_atoll(trimmed) != 0`
    ///
    /// Limitations (documented for users): only scalar string/int/float/
    /// bool params and returns are supported. Arrays/structs/`any` are
    /// NOT marshaled (phase 2 — full libpython embedding — is needed for
    /// that; see roadmap).
    fn compile_python_trampoline<'ctx>(
        &self,
        ctx:      &'ctx Context,
        module:   &Module<'ctx>,
        builder:  &Builder<'ctx>,
        builtins: &LlvmBuiltins<'ctx>,
        py_module: &str,
        f:        &ExternFnDecl,
        fv:       FunctionValue<'ctx>,
    ) -> R<()> {
        let _ = module;
        let entry = ctx.append_basic_block(fv, "entry");
        builder.position_at_end(entry);

        // code = "import {py_module}\nprint({py_module}.{name}("
        let prefix = format!("import {m}\nprint({m}.{fname}(", m = py_module, fname = f.name);
        let mut code: BasicValueEnum = builder.build_global_string_ptr(&prefix, ".pycode").unwrap()
        .as_pointer_value().into();

        let mut pidx = 0u32;
        for (i, p) in f.params.iter().enumerate() {
            let arg = fv.get_nth_param(pidx).ok_or_else(|| CodegenError::Llvm(format!("missing param {} for extern python fn {}", p.name, f.name)))?;
            pidx += 1;

            let marshaled: BasicValueEnum = if is_string_type(&p.ty) {
                let r = builder.build_call(builtins.hsh_py_repr, &[arg.into()], "pyrepr").unwrap();
                unwrap_call(ctx, r)
            } else {
                // numeric/bool: hsh_int_to_string produces a valid Python
                // int literal (e.g. "42", "-7"). Bools are passed as i8
                // 0/1 — also valid Python ints.
                let as_i64 = match arg {
                    BasicValueEnum::IntValue(iv) =>
                    builder.build_int_cast(iv, ctx.i64_type(), "to_i64").unwrap().into(),
                    BasicValueEnum::FloatValue(fval) =>
                    builder.build_float_to_signed_int(fval, ctx.i64_type(), "f2i").unwrap().into(),
                    other => other,
                };
                let r = builder.build_call(builtins.hsh_int_to_string, &[as_i64.into()], "argstr").unwrap();
                unwrap_call(ctx, r)
            };

            code = unwrap_call(ctx, builder.build_call(builtins.hsh_strcat, &[code.into(), marshaled.into()], "cat_arg").unwrap());

            if i + 1 < f.params.len() {
                let comma = builder.build_global_string_ptr(",", ".pycomma").unwrap().as_pointer_value();
                code = unwrap_call(ctx, builder.build_call(builtins.hsh_strcat, &[code.into(), comma.into()], "cat_comma").unwrap());
            }
        }

        let suffix = builder.build_global_string_ptr("))", ".pysuffix").unwrap().as_pointer_value();
        code = unwrap_call(ctx, builder.build_call(builtins.hsh_strcat, &[code.into(), suffix.into()], "cat_suffix").unwrap());

        // result = trim(py_eval(code))
        let raw     = unwrap_call(ctx, builder.build_call(builtins.hsh_py_eval, &[code.into()], "pyresult").unwrap());
        let trimmed = unwrap_call(ctx, builder.build_call(builtins.hsh_trim, &[raw.into()], "pytrim").unwrap());

        // Marshal back to the declared return type.
        let ret_val: Option<BasicValueEnum> = match &f.return_type {
            None => None,
            Some(ty) if is_string_type(ty) => Some(trimmed),
            Some(ty) if is_float_type(ty) => {
                let r = builder.build_call(builtins.hsh_atof, &[trimmed.into()], "pyfloat").unwrap();
                Some(unwrap_call(ctx, r))
            }
            Some(ty) if is_bool_type(ty) => {
                let r = builder.build_call(builtins.hsh_atoll, &[trimmed.into()], "pyint").unwrap();
                let iv = unwrap_call(ctx, r).into_int_value();
                let zero = iv.get_type().const_zero();
                let b = builder.build_int_compare(inkwell::IntPredicate::NE, iv, zero, "pybool").unwrap();
                Some(builder.build_int_z_extend(b, ctx.i8_type(), "pybool8").unwrap().into())
            }
            Some(_numeric) => {
                let r = builder.build_call(builtins.hsh_atoll, &[trimmed.into()], "pyint").unwrap();
                Some(unwrap_call(ctx, r))
            }
        };

        match ret_val {
            Some(v) => { builder.build_return(Some(&v)).unwrap(); }
            None    => { builder.build_return(None).unwrap(); }
        }
        Ok(())
    }

    fn emit_binary_with_machine(&self, module: &Module, machine: &TargetMachine) -> R<()> {
        let tmp_base = std::env::temp_dir().join(format!("hsharp_rt_{}", std::process::id()));
        let rt_c = format!("{}_rt.c",  tmp_base.display());
        let rt_o = format!("{}_rt.o",  tmp_base.display());
        std::fs::write(&rt_c, crate::runtime::runtime_c_source())?;
        let rt_opt = if self.opts.optimize { "-O2" } else { "-O0" };

        // The H# runtime uses PCRE2 (§11) and real libsqlite3 (§12), both
        // of which need their headers available at compile time.
        // pkg-config gives us the right include paths across distros.
        let mut rt_cflags: Vec<String> = vec![rt_opt.to_string(),
        "-ffunction-sections".into(), "-fdata-sections".into(), "-fPIC".into()];
        if self.opts.optimize {
            // Smaller/faster runtime object: H# never unwinds (panic =
            // abort), so omit unwind-table generation; frame pointers
            // aren't needed for backtraces we don't produce.
            rt_cflags.push("-fno-asynchronous-unwind-tables".into());
            rt_cflags.push("-fomit-frame-pointer".into());
        }
        for pkg in ["libpcre2-8", "sqlite3"] {
            if let Some(flags) = pkg_config_cflags(pkg) {
                rt_cflags.extend(flags);
            }
        }
        rt_cflags.push("-c".into());
        rt_cflags.push(rt_c.clone());
        rt_cflags.push("-o".into());
        rt_cflags.push(rt_o.clone());

        let ok = std::process::Command::new("cc")
        .args(&rt_cflags)
        .status()?.success();
        if !ok {
            return Err(CodegenError::Link(
                "runtime compile failed — is libpcre2-dev and libsqlite3-dev installed? \
(sudo apt install libpcre2-dev libsqlite3-dev)".into()
            ));
        }

        let obj_path = format!("{}_main.o", self.opts.output);
        machine.write_to_file(module, FileType::Object, Path::new(&obj_path))
        .map_err(|e| CodegenError::Llvm(e.to_string()))?;

        let has_main = module.get_function("main").is_some();
        if !has_main {
            let obj_out = format!("{}.o", self.opts.output);
            std::fs::copy(&obj_path, &obj_out).ok();
            eprintln!("  note: no `main` fn — compiled as object: {}", obj_out);
            std::fs::remove_file(&obj_path).ok();
            std::fs::remove_file(&rt_c).ok();
            std::fs::remove_file(&rt_o).ok();
            return Ok(());
        }

        let suffix = self.opts.target.exe_suffix();
        let out    = format!("{}{}", self.opts.output, suffix);

        // §11/§12 runtime link deps. Prefer pkg-config --libs (handles
        // e.g. Debian's `libpcre2-8` -> `-lpcre2-8`, and any extra deps
        // like -lz that pcre2 sometimes needs), falling back to a
        // hardcoded `-l{name}` guess.
        let mut runtime_libs: Vec<String> = Vec::new();
        for (pkg, fallback) in [("libpcre2-8", "-lpcre2-8"), ("sqlite3", "-lsqlite3")] {
            match pkg_config_libs(pkg) {
                Some(libs) => runtime_libs.extend(libs),
                None       => runtime_libs.push(fallback.to_string()),
            }
        }

        // §5: user `extern [c/cpp/rust, "lib"]` link flags (dynamic libs,
        // static libs with -Bstatic/-Bdynamic, and Rust staticlibs linked
        // --whole-archive). See ffi_linker.rs.
        let extern_args = self.link_flags.borrow().to_cc_args();

        let mut cmd = std::process::Command::new("cc");
        cmd.arg(&obj_path).arg(&rt_o).arg("-o").arg(&out);
        cmd.arg("-no-pie");
        cmd.args(["-lm", "-lpthread", "-ldl"]);
        for lib in &runtime_libs { cmd.arg(lib); }
        for a in &extern_args    { cmd.arg(a); }
        if self.opts.optimize {
            cmd.args(["-O2", "-Wl,--gc-sections", "-Wl,--as-needed",
                     "-Wl,--strip-all", "-flto"]);
        } else {
            cmd.arg("-O0");
        }
        if self.opts.static_link { cmd.arg("-static"); }

        let result = cmd.output()?;
        if !result.status.success() {
            // Retry without advanced linker flags (some distros' ld
            // chokes on --gc-sections + LTO combinations).
            let mut cmd2 = std::process::Command::new("cc");
            cmd2.arg(&obj_path).arg(&rt_o).arg("-o").arg(&out)
            .arg("-no-pie").args(["-lm", "-lpthread", "-ldl"]);
            for lib in &runtime_libs { cmd2.arg(lib); }
            for a in &extern_args    { cmd2.arg(a); }
            if self.opts.optimize { cmd2.arg("-O2"); }
            if self.opts.static_link { cmd2.arg("-static"); }
            let r2 = cmd2.output()?;
            if !r2.status.success() {
                let stderr = String::from_utf8_lossy(&result.stderr);
                let hint = if stderr.contains("pcre2") {
                    "\nhint: sudo apt install libpcre2-dev"
                } else if stderr.contains("sqlite3") {
                    "\nhint: sudo apt install libsqlite3-dev"
                } else if stderr.contains("cannot find -l") {
                    "\nhint: check `extern [c/cpp/rust, \"...\"]` library names and that -L search paths include them (LIBRARY_PATH env var)"
                } else {
                    ""
                };
                return Err(CodegenError::Link(format!("{}{}", stderr, hint)));
            }
        }

        if self.opts.optimize {
            let _ = std::process::Command::new("strip")
            .args(["--strip-all", "--strip-unneeded", &out])
            .status();
        }

        let _ = std::fs::remove_file(&obj_path);
        let _ = std::fs::remove_file(&rt_c);
        let _ = std::fs::remove_file(&rt_o);
        Ok(())
    }
}

/// Type-predicate helpers for the Python trampoline marshaling (above).
fn is_string_type(ty: &TypeExpr) -> bool {
    matches!(ty, TypeExpr::String) || matches!(ty, TypeExpr::Named(n) if n == "string")
}
fn is_float_type(ty: &TypeExpr) -> bool {
    matches!(ty, TypeExpr::F32 | TypeExpr::F64)
    || matches!(ty, TypeExpr::Named(n) if n == "f32" || n == "f64")
}
fn is_bool_type(ty: &TypeExpr) -> bool {
    matches!(ty, TypeExpr::Bool) || matches!(ty, TypeExpr::Named(n) if n == "bool")
}

/// Free-function version of `FnCx::unwrap_call`, usable from
/// `LlvmCodegen::compile_python_trampoline` (which has no `FnCx`).
fn unwrap_call<'ctx>(ctx: &'ctx Context, r: inkwell::values::CallSiteValue<'ctx>) -> BasicValueEnum<'ctx> {
    use inkwell::values::AnyValue;
    match r.as_any_value_enum() {
        inkwell::values::AnyValueEnum::IntValue(v)     => v.into(),
        inkwell::values::AnyValueEnum::FloatValue(v)   => v.into(),
        inkwell::values::AnyValueEnum::PointerValue(v) => v.into(),
        inkwell::values::AnyValueEnum::StructValue(v)  => v.into(),
        inkwell::values::AnyValueEnum::ArrayValue(v)   => v.into(),
        inkwell::values::AnyValueEnum::VectorValue(v)  => v.into(),
        _                                               => ctx.i64_type().const_zero().into(),
    }
}

// ── Per-function compile context ──────────────────────────────────────────

use inkwell::types::BasicMetadataTypeEnum;

/// Convert a BasicMetadataTypeEnum (function signature param type) back into
/// a BasicTypeEnum (value type hint). MetadataType has no Basic equivalent.
fn metadata_to_basic<'ctx>(t: BasicMetadataTypeEnum<'ctx>) -> Option<BasicTypeEnum<'ctx>> {
    match t {
        BasicMetadataTypeEnum::ArrayType(a)   => Some(a.into()),
        BasicMetadataTypeEnum::FloatType(f)   => Some(f.into()),
        BasicMetadataTypeEnum::IntType(i)     => Some(i.into()),
        BasicMetadataTypeEnum::PointerType(p) => Some(p.into()),
        BasicMetadataTypeEnum::StructType(s)  => Some(s.into()),
        BasicMetadataTypeEnum::VectorType(v)  => Some(v.into()),
        _ => None,
    }
}

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
    fn unwrap_call(&self, r: inkwell::values::CallSiteValue<'ctx>) -> BasicValueEnum<'ctx> {
        use inkwell::values::AnyValue;
        match r.as_any_value_enum() {
            inkwell::values::AnyValueEnum::IntValue(v)     => v.into(),
            inkwell::values::AnyValueEnum::FloatValue(v)   => v.into(),
            inkwell::values::AnyValueEnum::PointerValue(v) => v.into(),
            inkwell::values::AnyValueEnum::StructValue(v)  => v.into(),
            inkwell::values::AnyValueEnum::ArrayValue(v)   => v.into(),
            inkwell::values::AnyValueEnum::VectorValue(v)  => v.into(),
            _                                               => self.ctx.i64_type().const_zero().into(),
        }
    }

    fn stmts(&mut self, stmts: &[Stmt]) -> R<bool> {
        for stmt in stmts {
            if self.stmt(stmt)? { return Ok(true); }
        }
        Ok(false)
    }

    fn stmt(&mut self, s: &Stmt) -> R<bool> {
        match s {
            Stmt::Let { name, ty, value, .. } => {
                let llvm_ty = ty.as_ref()
                .and_then(|t| htype_to_llvm(self.ctx, t))
                .unwrap_or(self.ctx.i64_type().into());
                let ptr = self.builder.build_alloca(llvm_ty, name).unwrap();
                if let Some(e) = value {
                    let v = self.expr(e, Some(llvm_ty))?;
                    self.builder.build_store(ptr, v).unwrap();
                } else {
                    let z = self.zero(llvm_ty);
                    self.builder.build_store(ptr, z).unwrap();
                }
                self.vars.insert(name.clone(), ptr);
                Ok(false)
            }
            Stmt::Return(e, _) => {
                if let Some(expr) = e {
                    let hint = self.ret_type.as_ref().and_then(|t| htype_to_llvm(self.ctx, t));
                    let v    = self.expr(expr, hint)?;
                    let v    = self.coerce_ret(v);
                    self.builder.build_return(Some(&v)).unwrap();
                } else if self.fn_name == "main" {
                    let z = self.ctx.i32_type().const_int(0, false);
                    self.builder.build_return(Some(&z)).unwrap();
                } else {
                    self.builder.build_return(None).unwrap();
                }
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
                                let v = self.expr(rhs, None)?;
                                self.builder.build_store(ptr, v).unwrap();
                            }
                        }
                        Ok(false)
                    }
                    Expr::CompoundAssign(lhs, op, rhs, _) => {
                        if let Expr::Ident(name, _) = lhs.as_ref() {
                            if let Some(&ptr) = self.vars.get(name.as_str()) {
                                let lv  = self.builder.build_load(self.ctx.i64_type(), ptr, "lv").unwrap();
                                let rv  = self.expr(rhs, None)?;
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
            Stmt::Break(..) | Stmt::Continue(_) => {
                self.builder.build_unreachable().unwrap();
                Ok(true)
            }
            Stmt::Item(_) | Stmt::Import(..) => Ok(false),
        }
    }

    fn if_stmt(&mut self, cond: &Expr, then_b: &[Stmt],
               elsifs: &[(Expr, Vec<Stmt>)], else_b: &Option<Vec<Stmt>>) -> R<bool>
               {
                   let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                   let cv     = self.as_bool(cond)?;
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
                       if self.builder.get_insert_block()
                           .map(|b| b.get_terminator().is_none()).unwrap_or(false) {
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
                       let sv    = self.expr(start, Some(i64t.into()))?;
                       let ev    = self.expr(end_e,  Some(i64t.into()))?;
                       let loop_ptr = self.builder.build_alloca(i64t, vname).unwrap();
                       self.builder.build_store(loop_ptr, sv).unwrap();
                       self.vars.insert(vname.to_string(), loop_ptr);
                       let parent = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                       let header = self.ctx.append_basic_block(parent, "for_hdr");
                       let body_b = self.ctx.append_basic_block(parent, "for_body");
                       let exit   = self.ctx.append_basic_block(parent, "for_exit");
                       self.builder.build_unconditional_branch(header).unwrap();
                       self.builder.position_at_end(header);
                       let cur  = self.builder.build_load(i64t, loop_ptr, "cur").unwrap();
                       let cond = if *inclusive {
                           self.builder.build_int_compare(
                               inkwell::IntPredicate::SLE, cur.into_int_value(), ev.into_int_value(), "cmp").unwrap()
                       } else {
                           self.builder.build_int_compare(
                               inkwell::IntPredicate::SLT, cur.into_int_value(), ev.into_int_value(), "cmp").unwrap()
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

               fn expr(&mut self, e: &Expr, hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
                   match e {
                       Expr::Literal(lit, _) => self.literal(lit, hint),
                       Expr::Ident(name, _)  => {
                           let ptr = self.vars.get(name.as_str())
                           .copied()
                           .ok_or_else(|| CodegenError::UndefinedVar(name.clone()))?;
                           Ok(self.builder.build_load(self.ctx.i64_type(), ptr, name).unwrap())
                       }
                       Expr::BinOp(l, op, r, _) => {
                           let lv = self.expr(l, hint)?;
                           let rv = self.expr(r, hint)?;
                           // String concat for pointer + pointer
                           if matches!(op, BinOp::Add) {
                               if let (BasicValueEnum::PointerValue(_), BasicValueEnum::PointerValue(_)) = (&lv, &rv) {
                                   let r2 = self.builder.build_call(
                                       self.builtins.hsh_strcat, &[lv.into(), rv.into()], "cat").unwrap();
                                       return Ok(self.unwrap_call(r2));
                               }
                           }
                           self.binop(op, lv, rv)
                       }
                       Expr::UnOp(op, inner, _) => {
                           let v = self.expr(inner, hint)?;
                           Ok(match op {
                               UnOp::Neg => match v {
                                   BasicValueEnum::IntValue(i)   => self.builder.build_int_neg(i, "neg").unwrap().into(),
                              BasicValueEnum::FloatValue(f) => self.builder.build_float_neg(f, "fneg").unwrap().into(),
                              _                             => v,
                               },
                               UnOp::Not => {
                                   let i = v.into_int_value();
                                   let z = i.get_type().const_zero();
                                   self.builder.build_int_compare(inkwell::IntPredicate::EQ, i, z, "not").unwrap().into()
                               }
                               _ => v,
                           })
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
                       Expr::Try(inner, _) => {
                           let val = self.expr(inner, hint)?;
                           let fn_val = self.builder.get_insert_block()
                           .and_then(|b| b.get_parent()).unwrap();
                           let then_bb  = self.ctx.append_basic_block(fn_val, "try_err");
                           let merge_bb = self.ctx.append_basic_block(fn_val, "try_ok");
                           let zero     = self.ctx.i64_type().const_zero();
                           let is_err   = if let BasicValueEnum::IntValue(iv) = val {
                               self.builder.build_int_compare(inkwell::IntPredicate::EQ, iv, zero, "is_err").unwrap()
                           } else { self.ctx.bool_type().const_zero() };
                           self.builder.build_conditional_branch(is_err, then_bb, merge_bb).unwrap();
                           self.builder.position_at_end(then_bb);
                           self.builder.build_return(Some(&BasicValueEnum::IntValue(zero))).unwrap();
                           self.builder.position_at_end(merge_bb);
                           Ok(val)
                       }
                       Expr::Await(inner, _)    => self.expr(inner, hint),
                       Expr::Range(start, _, _, _) => self.expr(start, hint),
                       Expr::ArrayLit(elems, _) | Expr::TupleLit(elems, _) => {
                           // Allocate contiguous i64 slots via malloc; store each element; return base pointer.
                           let n   = elems.len().max(1) as u64;
                           let sz  = self.ctx.i64_type().const_int(n * 8, false);
                           let call = self.builder.build_call(
                               self.builtins.malloc, &[sz.into()], "arr_alloc").unwrap();
                               let base = self.unwrap_call(call);
                               if let BasicValueEnum::PointerValue(base_ptr) = base {
                                   for (i, e) in elems.iter().enumerate() {
                                       let v = self.expr(e, Some(self.ctx.i64_type().into()))?;
                                       let v64: BasicValueEnum = match v {
                                           BasicValueEnum::IntValue(iv) => iv.into(),
                                           BasicValueEnum::PointerValue(pv) =>
                                           self.builder.build_ptr_to_int(pv, self.ctx.i64_type(), "p2i").unwrap().into(),
                                           BasicValueEnum::FloatValue(fv) =>
                                           self.builder.build_bit_cast(fv, self.ctx.i64_type(), "f2i").unwrap(),
                                           other => other,
                                       };
                                       let idx = self.ctx.i64_type().const_int(i as u64, false);
                                       let elem_ptr = unsafe {
                                           self.builder.build_gep(self.ctx.i64_type(), base_ptr, &[idx], "elem_ptr").unwrap()
                                       };
                                       self.builder.build_store(elem_ptr, v64).unwrap();
                                   }
                                   Ok(base_ptr.into())
                               } else {
                                   Ok(self.ctx.i64_type().const_zero().into())
                               }
                       }
                       Expr::SelfExpr(_) => {
                           self.vars.get("self").map(|&ptr|
                           self.builder.build_load(self.ctx.i64_type(), ptr, "self").unwrap()
                           ).ok_or(CodegenError::UndefinedVar("self".into()))
                       }
                       _ => Ok(self.ctx.i64_type().const_zero().into()),
                   }
               }

               fn literal(&mut self, lit: &Literal, hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
                   Ok(match lit {
                       Literal::Int(n) => {
                           let t = match hint { Some(BasicTypeEnum::IntType(t)) => t, _ => self.ctx.i64_type() };
                           t.const_int(*n as u64, true).into()
                       }
                       Literal::Float(f) => {
                           let t = match hint { Some(BasicTypeEnum::FloatType(t)) => t, _ => self.ctx.f64_type() };
                           t.const_float(*f).into()
                       }
                       Literal::Bool(b)  => self.ctx.i8_type().const_int(if *b { 1 } else { 0 }, false).into(),
                      Literal::Nil      => self.ctx.i64_type().const_zero().into(),
                      Literal::String(s) => {
                          if let Some(&g) = self.str_globals.get(s.as_str()) {
                              g.into()
                          } else {
                              let gs = self.builder.build_global_string_ptr(s, ".str").unwrap();
                              let p  = gs.as_pointer_value();
                              self.str_globals.insert(s.clone(), p);
                              p.into()
                          }
                      }
                      Literal::Interpolated(parts) => {
                          let empty = self.builder.build_global_string_ptr("", ".istart").unwrap().as_pointer_value();
                          let mut acc: BasicValueEnum = empty.into();
                          for part in parts {
                              let pv: BasicValueEnum = match part {
                                  hsharp_parser::ast::InterpPart::Text(t) => {
                                      self.builder.build_global_string_ptr(t.as_str(), ".itext").unwrap()
                                      .as_pointer_value().into()
                                  }
                                  hsharp_parser::ast::InterpPart::Expr(e) => {
                                      let v  = self.expr(e, Some(self.ctx.i64_type().into()))?;
                                      let r  = self.builder.build_call(
                                          self.builtins.hsh_int_to_string, &[v.into()], "its").unwrap();
                                          self.unwrap_call(r).into()
                                  }
                              };
                              let r = self.builder.build_call(
                                  self.builtins.hsh_strcat, &[acc.into(), pv.into()], "cat").unwrap();
                                  acc = self.unwrap_call(r).into();
                          }
                          acc
                      }
                      Literal::Bytes(_) => self.ctx.i64_type().const_zero().into(),
                   })
               }

               fn call_fn(&mut self, name: &str, args: &[Expr], _hint: Option<BasicTypeEnum<'ctx>>) -> R<BasicValueEnum<'ctx>> {
                   let i8ptr = self.ctx.ptr_type(AddressSpace::default());
                   macro_rules! str_arg {
                       ($i:expr) => {
                           if let Some(a) = args.get($i) { self.expr(a, Some(i8ptr.into()))? }
                           else { self.builder.build_global_string_ptr("", ".empty").unwrap().as_pointer_value().into() }
                       }
                   }
                   macro_rules! call1 {
                       ($f:expr, $name:expr) => {{ let a = str_arg!(0); let r = self.builder.build_call($f, &[a.into()], $name).unwrap(); Ok(self.unwrap_call(r)) }}
                   }
                   macro_rules! call2 {
                       ($f:expr, $name:expr) => {{ let a = str_arg!(0); let b = str_arg!(1); let r = self.builder.build_call($f, &[a.into(), b.into()], $name).unwrap(); Ok(self.unwrap_call(r)) }}
                   }
                   macro_rules! call3 {
                       ($f:expr, $name:expr) => {{ let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let r = self.builder.build_call($f, &[a.into(), b.into(), c.into()], $name).unwrap(); Ok(self.unwrap_call(r)) }}
                   }
                   match name {
                       "write" | "writeln" | "println" => {
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
                           let a = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? }
                           else { self.ctx.i64_type().const_zero().into() };
                           let r = self.builder.build_call(self.builtins.hsh_int_to_string, &[a.into()], "ts").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       "len" => {
                           let a = str_arg!(0);
                           let r = self.builder.build_call(self.builtins.hsh_strlen, &[a.into()], "len").unwrap();
                           Ok(self.unwrap_call(r))
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
                               match v { BasicValueEnum::IntValue(i) => i, _ => self.ctx.i32_type().const_zero() }
                           } else { self.ctx.i32_type().const_zero() };
                           // Declare libc exit(i32) -> void locally (not part of LlvmBuiltins)
                           let exit_fn = self.module.get_function("exit").unwrap_or_else(|| {
                               let sig = self.ctx.void_type().fn_type(&[self.ctx.i32_type().into()], false);
                               self.module.add_function("exit", sig, Some(inkwell::module::Linkage::External))
                           });
                           self.builder.build_call(exit_fn, &[code.into()], "").unwrap();
                           self.builder.build_unreachable().unwrap();
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       "shell" | "cmd" => call1!(self.builtins.hsh_shell, "sh"),
                       // ── §0 SECURITY: shell-injection mitigations ──────────────────
                       "shell_escape" | "shquote" => call1!(self.builtins.hsh_shell_escape, "shq"),
                       // exec(cmd[,a1[,a2[,a3]]]) — direct fork+execve, no shell.
                       // Resolved by call arity to hsh_exec1..4.
                       "exec" => match args.len() {
                           0 | 1 => call1!(self.builtins.hsh_exec1, "exec1"),
                           2     => call2!(self.builtins.hsh_exec2, "exec2"),
                           3     => call3!(self.builtins.hsh_exec3, "exec3"),
                           _     => {
                               let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let d = str_arg!(3);
                               let r = self.builder.build_call(self.builtins.hsh_exec4, &[a.into(), b.into(), c.into(), d.into()], "exec4").unwrap();
                               Ok(self.unwrap_call(r))
                           }
                       },
                       // extern [python, "mod"] phase-1 bridge (manual py_eval calls)
                       "py_eval" => call1!(self.builtins.hsh_py_eval, "pyeval"),
                       "trim" | "str_trim" => call1!(self.builtins.hsh_trim, "trim"),
                       "to_lower" | "lower" => call1!(self.builtins.hsh_to_lower, "lower"),
                       "to_upper" | "upper" => call1!(self.builtins.hsh_to_upper, "upper"),
                       "contains" | "str_contains" => call2!(self.builtins.hsh_str_contains, "cont"),
                       "starts_with" => call2!(self.builtins.hsh_starts_with, "startsw"),
                       "ends_with"   => call2!(self.builtins.hsh_ends_with, "endsw"),
                       "replace" | "str_replace" => call3!(self.builtins.hsh_str_replace, "replace"),
                       "fs_write" | "write_file" => call2!(self.builtins.hsh_write_file, "fw"),
                       "fs_read"  | "read_file"  => call1!(self.builtins.hsh_read_file, "fr"),
                       "file_exists" | "fs_exists" => call1!(self.builtins.hsh_file_exists, "fexists"),
                       "fs_mkdir_all" | "mkdir_all" => call1!(self.builtins.hsh_mkdir_all, "mkdirall"),
                       "file_size_bytes" | "file_size" => call1!(self.builtins.hsh_file_size, "fsize"),
                       "is_dir" => call1!(self.builtins.hsh_is_dir, "isdir"),
                       "bold"        => call1!(self.builtins.hsh_bold, "bold"),
                       "green_text" | "green" => call1!(self.builtins.hsh_green_text, "grn"),
                       "red_text"   | "red"   => call1!(self.builtins.hsh_red_text, "red"),
                       "yellow_text"| "yellow"=> call1!(self.builtins.hsh_yellow_text, "yel"),
                       "dim_text"   | "dim"   => call1!(self.builtins.hsh_dim_text, "dim"),
                       "cyan_text"  | "cyan"  => call1!(self.builtins.hsh_cyan_text, "cyn"),
                       // ── Random / crypto ────────────────────────────────────────────
                       "random_hex" => {
                           let n = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? }
                           else { self.ctx.i64_type().const_int(8, false).into() };
                           let r = self.builder.build_call(self.builtins.hsh_random_hex, &[n.into()], "rndhex").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       "random_string" => {
                           let n = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? }
                           else { self.ctx.i64_type().const_int(8, false).into() };
                           let r = self.builder.build_call(self.builtins.hsh_random_string, &[n.into()], "rndstr").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       "random_int" => {
                           let lo = if let Some(e) = args.first() { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_zero().into() };
                           let hi = if let Some(e) = args.get(1)  { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_int(100, false).into() };
                           let r = self.builder.build_call(self.builtins.hsh_random_int, &[lo.into(), hi.into()], "rndint").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       "uuid_v4" | "new_uuid" => {
                           let r = self.builder.build_call(self.builtins.hsh_uuid_v4, &[], "uuid").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       // ── Regex (§11 — PCRE2) ────────────────────────────────────────
                       "regex_match" => {
                           let a = str_arg!(0); let b = str_arg!(1);
                           let r = self.builder.build_call(self.builtins.hsh_regex_match, &[a.into(), b.into()], "rxmatch").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       "regex_find"    => call2!(self.builtins.hsh_regex_find, "rxfind"),
                       "regex_replace" => call3!(self.builtins.hsh_regex_replace, "rxrepl"),
                       // ── SQLite (§12 — real libsqlite3, prepared statements) ────────
                       "sqlite_open"  => call1!(self.builtins.hsh_sqlite_open, "dbopen"),
                       "sqlite_exec"  => call2!(self.builtins.hsh_sqlite_exec, "dbexec"),
                       "sqlite_query" => call2!(self.builtins.hsh_sqlite_query, "dbquery"),
                       "sqlite_close" => {
                           let a = str_arg!(0);
                           self.builder.build_call(self.builtins.hsh_sqlite_close, &[a.into()], "").unwrap();
                           Ok(self.ctx.i64_type().const_zero().into())
                       }
                       // db_query_bind(db, sql, b1[, b2[, b3]]) — parameterized
                       // queries, SQL-injection-safe by construction (§12). Resolved
                       // by arity (3-5 args -> bind1/2/3) like exec()->exec1..4.
                       "db_query_bind" => match args.len() {
                           0 | 1 | 2 | 3 => call3!(self.builtins.hsh_sqlite_query_bind1, "dbbind1"),
                           4 => {
                               let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let d = str_arg!(3);
                               let r = self.builder.build_call(self.builtins.hsh_sqlite_query_bind2, &[a.into(), b.into(), c.into(), d.into()], "dbbind2").unwrap();
                               Ok(self.unwrap_call(r))
                           }
                           _ => {
                               let a = str_arg!(0); let b = str_arg!(1); let c = str_arg!(2); let d = str_arg!(3); let f5 = str_arg!(4);
                               let r = self.builder.build_call(self.builtins.hsh_sqlite_query_bind3, &[a.into(), b.into(), c.into(), d.into(), f5.into()], "dbbind3").unwrap();
                               Ok(self.unwrap_call(r))
                           }
                       },
                       // ── Network ─────────────────────────────────────────────────────
                       "dns_resolve" => call1!(self.builtins.hsh_dns_resolve, "dns"),
                       "http_get"    => call1!(self.builtins.hsh_http_get, "httpget"),
                       "http_post"   => call2!(self.builtins.hsh_http_post, "httppost"),
                       "json_get"    => call2!(self.builtins.hsh_json_get, "jsonget"),
                       "scan_port" => {
                           let host = str_arg!(0);
                           let port = if let Some(e) = args.get(1) { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_zero().into() };
                           let timeout = if let Some(e) = args.get(2) { self.expr(e, Some(self.ctx.i64_type().into()))? } else { self.ctx.i64_type().const_int(500, false).into() };
                           let r = self.builder.build_call(self.builtins.hsh_scan_port, &[host.into(), port.into(), timeout.into()], "scanport").unwrap();
                           Ok(self.unwrap_call(r))
                       }
                       _ => {
                           if let Some(&fv) = self.func_vals.get(name) {
                               let sig = fv.get_type();
                               let mut avs = Vec::new();
                               for (i, a) in args.iter().enumerate() {
                                   let expected: Option<BasicTypeEnum> = sig.get_param_types().get(i)
                                   .and_then(|pt| metadata_to_basic(*pt));
                                   avs.push(self.expr(a, expected)?);
                               }
                               let call_args: Vec<inkwell::values::BasicMetadataValueEnum> =
                               avs.iter().map(|v| (*v).into()).collect();
                               let r = self.builder.build_call(fv, &call_args, "call").unwrap();
                               if sig.get_return_type().is_none() {
                                   Ok(self.ctx.i64_type().const_zero().into())
                               } else {
                                   Ok(self.unwrap_call(r))
                               }
                           } else {
                               Ok(self.ctx.i64_type().const_zero().into())
                           }
                       }
                   }
               }

               fn binop(&mut self, op: &BinOp, lv: BasicValueEnum<'ctx>, rv: BasicValueEnum<'ctx>) -> R<BasicValueEnum<'ctx>> {
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
                      BinOp::Eq     => self.builder.build_int_compare(inkwell::IntPredicate::EQ,  l, r, "eq").unwrap().into(),
                      BinOp::NotEq  => self.builder.build_int_compare(inkwell::IntPredicate::NE,  l, r, "ne").unwrap().into(),
                      BinOp::Lt     => self.builder.build_int_compare(inkwell::IntPredicate::SLT, l, r, "lt").unwrap().into(),
                      BinOp::Gt     => self.builder.build_int_compare(inkwell::IntPredicate::SGT, l, r, "gt").unwrap().into(),
                      BinOp::LtEq   => self.builder.build_int_compare(inkwell::IntPredicate::SLE, l, r, "le").unwrap().into(),
                      BinOp::GtEq   => self.builder.build_int_compare(inkwell::IntPredicate::SGE, l, r, "ge").unwrap().into(),
                      BinOp::And    => self.builder.build_and(l, r, "land").unwrap().into(),
                      BinOp::Or     => self.builder.build_or(l, r, "lor").unwrap().into(),
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
                      _           => self.ctx.f64_type().const_zero().into(),
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
                      _ => v,
                   })
               }

               fn as_bool(&mut self, e: &Expr) -> R<inkwell::values::IntValue<'ctx>> {
                   let v = self.expr(e, Some(self.ctx.i8_type().into()))?;
                   match &v {
                       BasicValueEnum::IntValue(i) => {
                           let z = i.get_type().const_zero();
                           Ok(self.builder.build_int_compare(inkwell::IntPredicate::NE, *i, z, "bool").unwrap())
                       }
                       BasicValueEnum::FloatValue(f) => {
                           let z = f.get_type().const_float(0.0);
                           Ok(self.builder.build_float_compare(inkwell::FloatPredicate::ONE, *f, z, "fbool").unwrap())
                       }
                       _ => Ok(self.ctx.i8_type().const_int(1, false)),
                   }
               }

               fn coerce_ret(&mut self, v: BasicValueEnum<'ctx>) -> BasicValueEnum<'ctx> {
                   if self.fn_name != "main" { return v; }
                   let i32t = self.ctx.i32_type();
                   match v {
                       BasicValueEnum::IntValue(i) if i.get_type() != i32t =>
                       self.builder.build_int_cast(i, i32t, "ret_cast").unwrap().into(),
                       _ => v,
                   }
               }

               fn zero(&self, ty: BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
                   match ty {
                       BasicTypeEnum::IntType(t)     => t.const_zero().into(),
                       BasicTypeEnum::FloatType(t)   => t.const_zero().into(),
                       BasicTypeEnum::PointerType(t) => t.const_null().into(),
                       _                             => self.ctx.i64_type().const_zero().into(),
                   }
               }
}

/// §11/§12: query `pkg-config --cflags <pkg>` for compiler flags needed to
/// find PCRE2/sqlite3 headers. Returns `None` if `pkg-config` or the
/// package isn't available — callers fall back gracefully (relying on
/// default include paths, which works on most distros where these headers
/// live in /usr/include anyway).
fn pkg_config_cflags(pkg: &str) -> Option<Vec<String>> {
    let out = std::process::Command::new("pkg-config").args(["--cflags", pkg]).output().ok()?;
    if !out.status.success() { return None; }
    let s = String::from_utf8_lossy(&out.stdout);
    Some(s.split_whitespace().map(|s| s.to_string()).collect())
}

/// §11/§12: query `pkg-config --libs <pkg>` for the correct `-l...` link
/// flags (handles distro naming differences, e.g. `libpcre2-8` provides
/// `-lpcre2-8`, plus any extra transitive deps pkg-config knows about).
/// Returns `None` if unavailable — caller falls back to a hardcoded guess.
fn pkg_config_libs(pkg: &str) -> Option<Vec<String>> {
    let out = std::process::Command::new("pkg-config").args(["--libs", pkg]).output().ok()?;
    if !out.status.success() { return None; }
    let s = String::from_utf8_lossy(&out.stdout);
    let libs: Vec<String> = s.split_whitespace().map(|s| s.to_string()).collect();
    if libs.is_empty() { None } else { Some(libs) }
}
