use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::FunctionType;
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

pub struct LlvmBuiltins<'ctx> {
    // Core I/O
    pub hsh_println:       FunctionValue<'ctx>,
    pub hsh_print:         FunctionValue<'ctx>,
    pub hsh_panic:         FunctionValue<'ctx>,
    pub hsh_assert:        FunctionValue<'ctx>,
    pub hsh_int_to_string: FunctionValue<'ctx>,
    pub hsh_strlen:        FunctionValue<'ctx>,
    pub hsh_strcat:        FunctionValue<'ctx>,
    pub exit_fn:           FunctionValue<'ctx>,
    pub malloc:            FunctionValue<'ctx>,
    pub free:              FunctionValue<'ctx>,
    // String operations
    pub hsh_trim:          FunctionValue<'ctx>,
    pub hsh_to_upper:      FunctionValue<'ctx>,
    pub hsh_to_lower:      FunctionValue<'ctx>,
    pub hsh_str_contains:  FunctionValue<'ctx>,
    pub hsh_starts_with:   FunctionValue<'ctx>,
    pub hsh_ends_with:     FunctionValue<'ctx>,
    pub hsh_str_replace:   FunctionValue<'ctx>,
    // Time
    pub hsh_now_unix:      FunctionValue<'ctx>,
    pub hsh_now_ms:        FunctionValue<'ctx>,
    pub hsh_sleep_ms:      FunctionValue<'ctx>,
    // System
    pub hsh_shell:         FunctionValue<'ctx>,
    /// SECURITY (§0): POSIX single-quote escaping for untrusted data
    /// embedded into `shell()` commands.
    pub hsh_shell_escape:  FunctionValue<'ctx>,
    /// SECURITY (§0): direct fork+execve, no shell. exec(cmd[,a1[,a2[,a3]]])
    /// resolves to exec1..4 by call arity — see `codegen.rs::call_fn`.
    pub hsh_exec1:         FunctionValue<'ctx>,
    pub hsh_exec2:         FunctionValue<'ctx>,
    pub hsh_exec3:         FunctionValue<'ctx>,
    pub hsh_exec4:         FunctionValue<'ctx>,
    /// extern [python, "mod"] phase-1 bridge: execvp("python3", ["-c", code]).
    pub hsh_py_eval:       FunctionValue<'ctx>,
    /// Python string-literal escaping for marshaling H# string args into
    /// generated `py_eval` code (see `codegen.rs`'s Python trampoline gen).
    pub hsh_py_repr:       FunctionValue<'ctx>,
    /// Python trampoline return-value marshaling (string -> numeric).
    pub hsh_atoll:         FunctionValue<'ctx>,
    pub hsh_atof:          FunctionValue<'ctx>,
    pub hsh_getpid:        FunctionValue<'ctx>,
    pub hsh_hostname:      FunctionValue<'ctx>,
    // Random / Crypto
    pub hsh_random_hex:    FunctionValue<'ctx>,
    pub hsh_random_int:    FunctionValue<'ctx>,
    pub hsh_random_string: FunctionValue<'ctx>,
    pub hsh_uuid_v4:       FunctionValue<'ctx>,
    // Math
    pub hsh_sin:           FunctionValue<'ctx>,
    pub hsh_cos:           FunctionValue<'ctx>,
    pub hsh_sqrt:          FunctionValue<'ctx>,
    // Filesystem
    pub hsh_file_exists:   FunctionValue<'ctx>,
    pub hsh_read_file:     FunctionValue<'ctx>,
    pub hsh_write_file:    FunctionValue<'ctx>,
    pub hsh_mkdir_all:     FunctionValue<'ctx>,
    pub hsh_file_size:     FunctionValue<'ctx>,
    pub hsh_is_dir:        FunctionValue<'ctx>,
    // ANSI / Terminal
    pub hsh_bold:          FunctionValue<'ctx>,
    pub hsh_green_text:    FunctionValue<'ctx>,
    pub hsh_red_text:      FunctionValue<'ctx>,
    pub hsh_yellow_text:   FunctionValue<'ctx>,
    pub hsh_dim_text:      FunctionValue<'ctx>,
    pub hsh_cyan_text:     FunctionValue<'ctx>,
    // Network
    pub hsh_scan_port:     FunctionValue<'ctx>,
    pub hsh_dns_resolve:   FunctionValue<'ctx>,
    pub hsh_http_get:      FunctionValue<'ctx>,
    pub hsh_http_post:     FunctionValue<'ctx>,
    pub hsh_json_get:      FunctionValue<'ctx>,
    // Regex (§11 — PCRE2)
    pub hsh_regex_match:   FunctionValue<'ctx>,
    pub hsh_regex_find:    FunctionValue<'ctx>,
    pub hsh_regex_replace: FunctionValue<'ctx>,
    // SQLite (§12 — real libsqlite3, prepared statements)
    pub hsh_sqlite_open:        FunctionValue<'ctx>,
    pub hsh_sqlite_exec:        FunctionValue<'ctx>,
    pub hsh_sqlite_query:       FunctionValue<'ctx>,
    pub hsh_sqlite_query_bind1: FunctionValue<'ctx>,
    pub hsh_sqlite_query_bind2: FunctionValue<'ctx>,
    pub hsh_sqlite_query_bind3: FunctionValue<'ctx>,
    pub hsh_sqlite_close:       FunctionValue<'ctx>,
}

impl<'ctx> LlvmBuiltins<'ctx> {
    pub fn declare(ctx: &'ctx Context, module: &Module<'ctx>) -> Self {
        let ptr  = ctx.ptr_type(AddressSpace::default());
        let i64t = ctx.i64_type();
        let i32t = ctx.i32_type();
        let i8t  = ctx.i8_type();
        let f64t = ctx.f64_type();
        let void = ctx.void_type();

        let decl = |name: &str, fn_type: FunctionType<'ctx>| -> FunctionValue<'ctx> {
            module.get_function(name).unwrap_or_else(|| module.add_function(name, fn_type, None))
        };
        let pp   = |name: &str| decl(name, ptr.fn_type(&[ptr.into()], false));         // ptr->ptr
        let ip   = |name: &str| decl(name, ptr.fn_type(&[i64t.into()], false));        // i64->ptr
        let pi   = |name: &str| decl(name, i64t.fn_type(&[ptr.into()], false));        // ptr->i64
        let ppi  = |name: &str| decl(name, i64t.fn_type(&[ptr.into(), ptr.into()], false)); // ptr,ptr->i64
        let ppp  = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into()], false));  // ptr,ptr->ptr
        let pppp = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into()], false)); // ptr,ptr,ptr->ptr
        let p4   = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into()], false)); // 4 ptr->ptr
        let p5   = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into(), ptr.into()], false)); // 5 ptr->ptr
        let _vp  = |name: &str| decl(name, void.fn_type(&[ptr.into()], false));        // ptr->void
        let ni   = |name: &str| decl(name, i64t.fn_type(&[], false));                  // ->i64
        let np   = |name: &str| decl(name, ptr.fn_type(&[], false));                   // ->ptr
        let vi   = |name: &str| decl(name, void.fn_type(&[i64t.into()], false));       // i64->void
        let vp   = |name: &str| decl(name, void.fn_type(&[ptr.into()], false));        // ptr->void
        let ff   = |name: &str| decl(name, f64t.fn_type(&[f64t.into()], false));       // f64->f64

        Self {
            // Core
            hsh_println:       decl("hsh_println",       void.fn_type(&[ptr.into()],  false)),
            hsh_print:         decl("hsh_print",         void.fn_type(&[ptr.into()],  false)),
            hsh_panic:         decl("hsh_panic",         void.fn_type(&[ptr.into()],  false)),
            hsh_assert:        decl("hsh_assert",        void.fn_type(&[i8t.into(), ptr.into()], false)),
            hsh_int_to_string: decl("hsh_int_to_string", ptr.fn_type(&[i64t.into()],  false)),
            hsh_strlen:        decl("hsh_strlen",        i64t.fn_type(&[ptr.into()],  false)),
            hsh_strcat:        decl("hsh_strcat",        ptr.fn_type(&[ptr.into(), ptr.into()], false)),
            exit_fn:           decl("exit",              void.fn_type(&[i32t.into()], false)),
            malloc:            decl("malloc",            ptr.fn_type(&[i64t.into()],  false)),
            free:              decl("free",              void.fn_type(&[ptr.into()],  false)),
            // String
            hsh_trim:          pp("hsh_trim"),
            hsh_to_upper:      pp("hsh_to_upper"),
            hsh_to_lower:      pp("hsh_to_lower"),
            hsh_str_contains:  ppi("hsh_str_contains"),
            hsh_starts_with:   ppi("hsh_starts_with"),
            hsh_ends_with:     ppi("hsh_ends_with"),
            hsh_str_replace:   pppp("hsh_str_replace"),
            // Time
            hsh_now_unix:      ni("hsh_now_unix"),
            hsh_now_ms:        ni("hsh_now_ms"),
            hsh_sleep_ms:      vi("hsh_sleep_ms"),
            // System
            hsh_shell:         pp("hsh_shell"),
            hsh_shell_escape:  pp("hsh_shell_escape"),
            hsh_exec1:         pp("hsh_exec1"),
            hsh_exec2:         ppp("hsh_exec2"),
            hsh_exec3:         pppp("hsh_exec3"),
            hsh_exec4:         p4("hsh_exec4"),
            hsh_py_eval:       pp("hsh_py_eval"),
            hsh_py_repr:       pp("hsh_py_repr"),
            hsh_atoll:         decl("hsh_atoll", i64t.fn_type(&[ptr.into()], false)),
            hsh_atof:          decl("hsh_atof",  f64t.fn_type(&[ptr.into()], false)),
            hsh_getpid:        ni("hsh_getpid"),
            hsh_hostname:      np("hsh_hostname"),
            // Random
            hsh_random_hex:    ip("hsh_random_hex"),
            hsh_random_int:    decl("hsh_random_int",   i64t.fn_type(&[i64t.into(), i64t.into()], false)),
            hsh_random_string: ip("hsh_random_string"),
            hsh_uuid_v4:       np("hsh_uuid_v4"),
            // Math
            hsh_sin:           ff("hsh_sin"),
            hsh_cos:           ff("hsh_cos"),
            hsh_sqrt:          ff("hsh_sqrt"),
            // Filesystem
            hsh_file_exists:   pi("hsh_file_exists"),
            hsh_read_file:     pp("hsh_read_file"),
            hsh_write_file:    decl("hsh_write_file",   i64t.fn_type(&[ptr.into(), ptr.into()], false)),
            hsh_mkdir_all:     pi("hsh_mkdir_all"),
            hsh_file_size:     pi("hsh_file_size"),
            hsh_is_dir:        pi("hsh_is_dir"),
            // ANSI
            hsh_bold:          pp("hsh_bold"),
            hsh_green_text:    pp("hsh_green_text"),
            hsh_red_text:      pp("hsh_red_text"),
            hsh_yellow_text:   pp("hsh_yellow_text"),
            hsh_dim_text:      pp("hsh_dim_text"),
            hsh_cyan_text:     pp("hsh_cyan_text"),
            // Network
            hsh_scan_port:     decl("hsh_scan_port_net", i64t.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_dns_resolve:   pp("hsh_dns_resolve"),
            hsh_http_get:      pp("hsh_http_get"),
            hsh_http_post:     ppp("hsh_http_post"),
            hsh_json_get:      ppp("hsh_json_get"),
            // Regex (PCRE2)
            hsh_regex_match:   ppi("hsh_regex_match"),
            hsh_regex_find:    ppp("hsh_regex_find"),
            hsh_regex_replace: pppp("hsh_regex_replace"),
            // SQLite (real libsqlite3)
            hsh_sqlite_open:        pp("hsh_sqlite_open"),
            hsh_sqlite_exec:        ppp("hsh_sqlite_exec"),
            hsh_sqlite_query:       ppp("hsh_sqlite_query"),
            hsh_sqlite_query_bind1: pppp("hsh_sqlite_query_bind1"),
            hsh_sqlite_query_bind2: p4("hsh_sqlite_query_bind2"),
            hsh_sqlite_query_bind3: p5("hsh_sqlite_query_bind3"),
            hsh_sqlite_close:       vp("hsh_sqlite_close"),
        }
    }
}
