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
    pub hsh_val_to_str:    FunctionValue<'ctx>,
    /// `@arena`-mode support (see codegen.rs's compile_fn/build_return_coerced):
    /// hsh_arena_new(cap) creates a bump-allocator arena; hsh_arena_push_current
    /// / hsh_arena_pop_current mark it as "the current arena" for the duration
    /// of the annotated function's call (so array_new/struct_new/strcat and
    /// friends allocate from it instead of straight malloc); hsh_arena_free
    /// reclaims the whole thing in one shot on every exit path.
    pub hsh_arena_new:            FunctionValue<'ctx>,
    /// `unsafe arena(kind, N)`/`unsafe pool(N)`/`unsafe page`/`unsafe
    /// ring(N)` blocks (see parser.rs's `parse_unsafe_block` and
    /// codegen.rs's `Expr::Unsafe` handling): unlike `hsh_arena_new`
    /// (always General-kind, used by plain `@arena` functions), this
    /// creates an arena tagged with the requested `ArenaKind` so
    /// `hsh_arena_alloc` in core.c can actually give Fixed/Pool/Page/Ring
    /// their documented, previously-nonexistent distinct behavior
    /// (panic-on-overflow / uniform chunk size / page alignment /
    /// overwrite-oldest-on-wrap, respectively).
    pub hsh_arena_new_kind:       FunctionValue<'ctx>,
    pub hsh_arena_free:           FunctionValue<'ctx>,
    /// `@arena` basic v2 — checkpoint/rewind for reusing part of an
    /// arena's lifetime, plus usage introspection. See core.c.
    pub hsh_arena_checkpoint:     FunctionValue<'ctx>,
    pub hsh_arena_rewind:         FunctionValue<'ctx>,
    pub hsh_arena_used:           FunctionValue<'ctx>,
    pub hsh_arena_capacity:       FunctionValue<'ctx>,
    pub hsh_arena_push_current:   FunctionValue<'ctx>,
    pub hsh_arena_pop_current:    FunctionValue<'ctx>,
    /// `@arc` basic v2 — manual atomic refcounting primitives (see
    /// core.c), plus automatic retain-on-assign/release-on-scope-exit
    /// for straight-line top-level bindings (see codegen.rs's
    /// `Stmt::Let` handling and `emit_arc_epilogue`). Still directly
    /// callable too, as `arc_alloc(n)` / `arc_retain(x)` /
    /// `arc_release(x)` / `arc_count(x)` (see call_fn in codegen.rs).
    pub hsh_rc_alloc:   FunctionValue<'ctx>,
    pub hsh_rc_retain:  FunctionValue<'ctx>,
    pub hsh_rc_release: FunctionValue<'ctx>,
    pub hsh_rc_count:   FunctionValue<'ctx>,
    /// `@arc` weak references (see core.c). `arc_downgrade`/
    /// `arc_upgrade`/`arc_weak_release`/`arc_weak_count` — lets a cyclic
    /// structure break the cycle by making one direction weak, so the
    /// cycle doesn't keep every node alive forever (the exact gap plain
    /// strong-only refcounting always has).
    pub hsh_arc_downgrade:    FunctionValue<'ctx>,
    pub hsh_arc_upgrade:      FunctionValue<'ctx>,
    pub hsh_arc_weak_release: FunctionValue<'ctx>,
    pub hsh_arc_weak_count:   FunctionValue<'ctx>,
    /// `@pointers` basic v2 — raw, unchecked memory access at every
    /// common width, plus a pointer-to-pointer variant (see core.c).
    pub hsh_ptr_read_i64:  FunctionValue<'ctx>,
    pub hsh_ptr_write_i64: FunctionValue<'ctx>,
    pub hsh_ptr_read_i32:  FunctionValue<'ctx>,
    pub hsh_ptr_write_i32: FunctionValue<'ctx>,
    pub hsh_ptr_read_i16:  FunctionValue<'ctx>,
    pub hsh_ptr_write_i16: FunctionValue<'ctx>,
    pub hsh_ptr_read_i8:   FunctionValue<'ctx>,
    pub hsh_ptr_write_i8:  FunctionValue<'ctx>,
    pub hsh_ptr_read_f64:  FunctionValue<'ctx>,
    pub hsh_ptr_write_f64: FunctionValue<'ctx>,
    pub hsh_ptr_read_f32:  FunctionValue<'ctx>,
    pub hsh_ptr_write_f32: FunctionValue<'ctx>,
    pub hsh_ptr_read_ptr:  FunctionValue<'ctx>,
    pub hsh_ptr_write_ptr: FunctionValue<'ctx>,
    pub hsh_ptr_is_null:   FunctionValue<'ctx>,
    pub hsh_ptr_add:       FunctionValue<'ctx>,
    /// `@pointers` basic v3 — see core.c: allocation-size introspection
    /// (arc_alloc pointers only) and memcpy/memcmp-equivalent bulk ops.
    pub hsh_ptr_alloc_size: FunctionValue<'ctx>,
    pub hsh_ptr_copy:       FunctionValue<'ctx>,
    pub hsh_ptr_compare:    FunctionValue<'ctx>,
    /// `@pointers` basic v4 — memset-equivalents. See core.c.
    pub hsh_ptr_fill: FunctionValue<'ctx>,
    pub hsh_ptr_zero: FunctionValue<'ctx>,
    /// `@pointers` basic v4 — opt-in bounds-checked read/write (see
    /// core.c). `hsh_panic`s on out-of-bounds instead of silently
    /// corrupting memory.
    pub hsh_ptr_read_checked:  FunctionValue<'ctx>,
    pub hsh_ptr_write_checked: FunctionValue<'ctx>,
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
    pub hsh_shell_escape:  FunctionValue<'ctx>,
    // proc::run_cmd / proc::run_cmd_live — see runtime/core.c's doc
    // comment above hsh_run_cmd_exec for why this is 3 plain-scalar
    // functions instead of one struct-returning one.
    pub hsh_run_cmd_exec:         FunctionValue<'ctx>,
    pub hsh_run_cmd_last_stdout:  FunctionValue<'ctx>,
    pub hsh_run_cmd_last_stderr:  FunctionValue<'ctx>,
    // str::split — see runtime/core.c's doc comment above
    // hsh_str_split_count for why this is two scalar-return functions
    // instead of one that hands back an array.
    pub hsh_str_split_count: FunctionValue<'ctx>,
    pub hsh_str_split_part:  FunctionValue<'ctx>,
    pub hsh_exec1:         FunctionValue<'ctx>,
    pub hsh_exec2:         FunctionValue<'ctx>,
    pub hsh_exec3:         FunctionValue<'ctx>,
    pub hsh_exec4:         FunctionValue<'ctx>,
    pub hsh_py_eval:       FunctionValue<'ctx>,
    pub hsh_py_repr:       FunctionValue<'ctx>,
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
    // Both hsh_remove_file/hsh_rename already existed in core.c but were
    // never wired to a callable H# name — fs::remove/fs::rename mangle
    // to "fs_remove"/"fs_rename", which resolved to neither a user fn
    // nor a builtin. Zero new C code, just plumbing.
    pub hsh_remove_file:   FunctionValue<'ctx>,
    pub hsh_rename:        FunctionValue<'ctx>,
    pub hsh_remove_dir_recursive: FunctionValue<'ctx>,
    pub hsh_int_to_str:    FunctionValue<'ctx>,
    pub hsh_str_to_int:    FunctionValue<'ctx>,
    pub hsh_env_get:       FunctionValue<'ctx>,
    pub hsh_env_read_line: FunctionValue<'ctx>,
    pub hsh_json_set_str:  FunctionValue<'ctx>,
    // math:: — wrappers around libm, already implemented in core.c but
    // never wired to a callable name until now.
    pub hsh_tan: FunctionValue<'ctx>,
    pub hsh_pow: FunctionValue<'ctx>,
    pub hsh_floor: FunctionValue<'ctx>,
    pub hsh_ceil: FunctionValue<'ctx>,
    pub hsh_abs_f: FunctionValue<'ctx>,
    pub hsh_abs_i: FunctionValue<'ctx>,
    pub hsh_min_i: FunctionValue<'ctx>,
    pub hsh_max_i: FunctionValue<'ctx>,
    pub hsh_min_f: FunctionValue<'ctx>,
    pub hsh_max_f: FunctionValue<'ctx>,
    // os:: / time:: — same story: hsh_hostname/hsh_getpid/hsh_sleep_ms/
    // hsh_now_unix/hsh_now_ms already existed in core.c AND were
    // already declared here, unwired to a callable name (see
    // codegen.rs). hsh_getcwd/hsh_username/hsh_platform/hsh_setenv are
    // newly declared.
    pub hsh_getcwd: FunctionValue<'ctx>,
    pub hsh_chdir: FunctionValue<'ctx>,
    pub hsh_username: FunctionValue<'ctx>,
    pub hsh_platform: FunctionValue<'ctx>,
    pub hsh_setenv: FunctionValue<'ctx>,
    // encoding:: base64 / url — new in core.c, gcc-tested (see
    // docs/CHANGES-I-MADE.md's stdlib audit section).
    pub hsh_base64_encode: FunctionValue<'ctx>,
    pub hsh_base64_decode: FunctionValue<'ctx>,
    pub hsh_url_encode: FunctionValue<'ctx>,
    pub hsh_url_decode: FunctionValue<'ctx>,
    // HashMap — see runtime/core.c's doc comment above HshMap's typedef.
    // `hsh_map_new(string_keys: i64)`: 0 = int64 keys, 1 = string keys
    // (content hash/eq) — see codegen.rs's "map_new" dispatch for how the
    // H# caller's declared key type selects which to pass.
    pub hsh_map_new:    FunctionValue<'ctx>,
    pub hsh_map_set:    FunctionValue<'ctx>,
    pub hsh_map_get:    FunctionValue<'ctx>,
    pub hsh_map_has:    FunctionValue<'ctx>,
    pub hsh_map_remove: FunctionValue<'ctx>,
    pub hsh_map_len:    FunctionValue<'ctx>,
    pub hsh_map_keys:   FunctionValue<'ctx>,
    pub hsh_map_clear:  FunctionValue<'ctx>,
    pub hsh_is_dir:        FunctionValue<'ctx>,
    /// Real C implementations that already existed in `core.c`
    /// (`hsh_is_file`/`hsh_append_file`) but had no `LlvmBuiltins` field
    /// or dispatch arm at all — added here to back `std/fs.h#`'s
    /// `is_file`/`append` for the LLVM backend (they already worked on
    /// the interpreter, via `call.rs`'s own separate arms).
    pub hsh_is_file:       FunctionValue<'ctx>,
    pub hsh_append_file:   FunctionValue<'ctx>,
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
    // SQLite (§12)
    pub hsh_sqlite_open:        FunctionValue<'ctx>,
    pub hsh_sqlite_exec:        FunctionValue<'ctx>,
    pub hsh_sqlite_query:       FunctionValue<'ctx>,
    pub hsh_sqlite_query_bind1: FunctionValue<'ctx>,
    pub hsh_sqlite_query_bind2: FunctionValue<'ctx>,
    pub hsh_sqlite_query_bind3: FunctionValue<'ctx>,
    pub hsh_sqlite_close:       FunctionValue<'ctx>,
    // ── Dynamic arrays (HshArray*) ────────────────────────────────────────
    pub hsh_array_new:     FunctionValue<'ctx>,
    pub hsh_array_push:    FunctionValue<'ctx>,
    pub hsh_array_len:     FunctionValue<'ctx>,
    pub hsh_array_get:     FunctionValue<'ctx>,
    pub hsh_array_set:     FunctionValue<'ctx>,
    pub hsh_array_concat:  FunctionValue<'ctx>,
    pub hsh_array_contains: FunctionValue<'ctx>,
    // ── env::args() ──────────────────────────────────────────────────────
    pub hsh_env_args:      FunctionValue<'ctx>,
    // ── Struct helpers ────────────────────────────────────────────────────
    pub hsh_struct_new:    FunctionValue<'ctx>,
    pub hsh_struct_get:    FunctionValue<'ctx>,
    pub hsh_struct_set:    FunctionValue<'ctx>,
    // ── Extra string helpers ──────────────────────────────────────────────
    pub hsh_string_split:  FunctionValue<'ctx>,
    pub hsh_string_find:   FunctionValue<'ctx>,
    pub hsh_string_rfind:  FunctionValue<'ctx>,
    pub hsh_string_slice:  FunctionValue<'ctx>,
    pub hsh_string_at:     FunctionValue<'ctx>,
    pub hsh_string_pad_right: FunctionValue<'ctx>,
    pub hsh_string_repeat: FunctionValue<'ctx>,
    pub hsh_string_trim_right: FunctionValue<'ctx>,
    pub hsh_to_int:        FunctionValue<'ctx>,
    pub hsh_to_int_from_hex: FunctionValue<'ctx>,
    pub hsh_to_float_fn:   FunctionValue<'ctx>,
    pub hsh_proc_id:       FunctionValue<'ctx>,
    pub hsh_file_delete:   FunctionValue<'ctx>,
    pub hsh_dir_create:    FunctionValue<'ctx>,
    pub hsh_dir_exists:    FunctionValue<'ctx>,
    // Extra aliases
    pub hsh_readline:        FunctionValue<'ctx>,
    pub hsh_string_chars:    FunctionValue<'ctx>,
    pub hsh_dir_remove_all:  FunctionValue<'ctx>,
    pub hsh_bytes_to_string: FunctionValue<'ctx>,
    pub hsh_string_to_bytes: FunctionValue<'ctx>,
    pub hsh_string_contains: FunctionValue<'ctx>,
    pub hsh_string_replace:  FunctionValue<'ctx>,
    pub hsh_string_trim:     FunctionValue<'ctx>,
    pub hsh_string_upper:    FunctionValue<'ctx>,
    pub hsh_string_lower:    FunctionValue<'ctx>,
    pub hsh_string_starts_with: FunctionValue<'ctx>,
    pub hsh_string_ends_with:   FunctionValue<'ctx>,
    pub hsh_string_len:      FunctionValue<'ctx>,
    pub hsh_array_remove:    FunctionValue<'ctx>,
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
        let pp   = |name: &str| decl(name, ptr.fn_type(&[ptr.into()], false));
        let ip   = |name: &str| decl(name, ptr.fn_type(&[i64t.into()], false));
        let pi   = |name: &str| decl(name, i64t.fn_type(&[ptr.into()], false));
        let ppi  = |name: &str| decl(name, i64t.fn_type(&[ptr.into(), ptr.into()], false));
        let ppp  = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into()], false));
        let pppp = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into()], false));
        let p4   = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into()], false));
        let p5   = |name: &str| decl(name, ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into(), ptr.into()], false));
        let ni   = |name: &str| decl(name, i64t.fn_type(&[], false));
        let np   = |name: &str| decl(name, ptr.fn_type(&[], false));
        let vi   = |name: &str| decl(name, void.fn_type(&[i64t.into()], false));
        let vp   = |name: &str| decl(name, void.fn_type(&[ptr.into()], false));
        let ff   = |name: &str| decl(name, f64t.fn_type(&[f64t.into()], false));

        Self {
            // Core
            hsh_println:       decl("hsh_println",       void.fn_type(&[ptr.into()],  false)),
            hsh_print:         decl("hsh_print",         void.fn_type(&[ptr.into()],  false)),
            hsh_panic:         decl("hsh_panic",         void.fn_type(&[ptr.into()],  false)),
            hsh_assert:        decl("hsh_assert",        void.fn_type(&[i8t.into(), ptr.into()], false)),
            hsh_int_to_string: decl("hsh_int_to_string", ptr.fn_type(&[i64t.into()],  false)),
            hsh_val_to_str:    decl("hsh_val_to_str",    ptr.fn_type(&[i64t.into()],  false)),
            hsh_arena_new:          ip("hsh_arena_new"),
            hsh_arena_new_kind:     decl("hsh_arena_new_kind", ptr.fn_type(&[i64t.into(), i64t.into()], false)),
            hsh_arena_free:         vp("hsh_arena_free"),
            hsh_arena_checkpoint:   ni("hsh_arena_checkpoint"),
            hsh_arena_rewind:       decl("hsh_arena_rewind", void.fn_type(&[i64t.into()], false)),
            hsh_arena_used:         ni("hsh_arena_used"),
            hsh_arena_capacity:     ni("hsh_arena_capacity"),
            hsh_arena_push_current: vp("hsh_arena_push_current"),
            hsh_arena_pop_current:  np("hsh_arena_pop_current"),
            hsh_rc_alloc:           ip("hsh_rc_alloc"),
            hsh_rc_retain:          vp("hsh_rc_retain"),
            hsh_rc_release:         vp("hsh_rc_release"),
            hsh_rc_count:           pi("hsh_rc_count"),
            hsh_arc_downgrade:      pp("hsh_arc_downgrade"),
            hsh_arc_upgrade:        pp("hsh_arc_upgrade"),
            hsh_arc_weak_release:   vp("hsh_arc_weak_release"),
            hsh_arc_weak_count:     pi("hsh_arc_weak_count"),
            hsh_ptr_read_i64:  decl("hsh_ptr_read_i64",  i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_i64: decl("hsh_ptr_write_i64", void.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_ptr_read_i32:  decl("hsh_ptr_read_i32",  i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_i32: decl("hsh_ptr_write_i32", void.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_ptr_read_i16:  decl("hsh_ptr_read_i16",  i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_i16: decl("hsh_ptr_write_i16", void.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_ptr_read_i8:   decl("hsh_ptr_read_i8",   i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_i8:  decl("hsh_ptr_write_i8",  void.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_ptr_read_f64:  decl("hsh_ptr_read_f64",  f64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_f64: decl("hsh_ptr_write_f64", void.fn_type(&[ptr.into(), i64t.into(), f64t.into()], false)),
            hsh_ptr_read_f32:  decl("hsh_ptr_read_f32",  f64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_f32: decl("hsh_ptr_write_f32", void.fn_type(&[ptr.into(), i64t.into(), f64t.into()], false)),
            hsh_ptr_read_ptr:  decl("hsh_ptr_read_ptr",  ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_write_ptr: decl("hsh_ptr_write_ptr", void.fn_type(&[ptr.into(), i64t.into(), ptr.into()], false)),
            hsh_ptr_is_null:        pi("hsh_ptr_is_null"),
            hsh_ptr_add:       decl("hsh_ptr_add",       ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_alloc_size: pi("hsh_ptr_alloc_size"),
            hsh_ptr_copy:       decl("hsh_ptr_copy",    void.fn_type(&[ptr.into(), ptr.into(), i64t.into()], false)),
            hsh_ptr_compare:    decl("hsh_ptr_compare", i64t.fn_type(&[ptr.into(), ptr.into(), i64t.into()], false)),
            hsh_ptr_fill: decl("hsh_ptr_fill", void.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_ptr_zero: decl("hsh_ptr_zero", void.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_ptr_read_checked:  decl("hsh_ptr_read_checked",  i64t.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_ptr_write_checked: decl("hsh_ptr_write_checked", void.fn_type(&[ptr.into(), i64t.into(), i64t.into(), i64t.into()], false)),
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
            hsh_run_cmd_exec:        decl("hsh_run_cmd_exec",
                i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_run_cmd_last_stdout: np("hsh_run_cmd_last_stdout"),
            hsh_run_cmd_last_stderr: np("hsh_run_cmd_last_stderr"),
            hsh_str_split_count: decl("hsh_str_split_count",
                i64t.fn_type(&[ptr.into(), ptr.into()], false)),
            hsh_str_split_part: decl("hsh_str_split_part",
                ptr.fn_type(&[ptr.into(), ptr.into(), i64t.into()], false)),
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
            hsh_random_int:    decl("hsh_random_int", i64t.fn_type(&[i64t.into(), i64t.into()], false)),
            hsh_random_string: ip("hsh_random_string"),
            hsh_uuid_v4:       np("hsh_uuid_v4"),
            // Math
            hsh_sin:           ff("hsh_sin"),
            hsh_cos:           ff("hsh_cos"),
            hsh_sqrt:          ff("hsh_sqrt"),
            // Filesystem
            hsh_file_exists:   pi("hsh_file_exists"),
            hsh_read_file:     pp("hsh_read_file"),
            hsh_write_file:    decl("hsh_write_file", i64t.fn_type(&[ptr.into(), ptr.into()], false)),
            hsh_mkdir_all:     pi("hsh_mkdir_all"),
            hsh_file_size:     pi("hsh_file_size"),
            hsh_remove_file:   pi("hsh_remove_file"),
            hsh_rename:        ppi("hsh_rename"),
            hsh_remove_dir_recursive: pi("hsh_remove_dir_recursive"),
            hsh_int_to_str:    ip("hsh_int_to_str"),
            hsh_str_to_int:    pi("hsh_str_to_int"),
            hsh_env_get:       pp("hsh_env_get"),
            hsh_env_read_line: np("hsh_env_read_line"),
            hsh_json_set_str:  decl("hsh_json_set_str",
                ptr.fn_type(&[ptr.into(), ptr.into(), ptr.into()], false)),
            hsh_tan: ff("hsh_tan"),
            hsh_pow: decl("hsh_pow", f64t.fn_type(&[f64t.into(), f64t.into()], false)),
            hsh_floor: ff("hsh_floor"),
            hsh_ceil: ff("hsh_ceil"),
            hsh_abs_f: ff("hsh_abs_f"),
            hsh_abs_i: decl("hsh_abs_i", i64t.fn_type(&[i64t.into()], false)),
            hsh_min_i: decl("hsh_min_i", i64t.fn_type(&[i64t.into(), i64t.into()], false)),
            hsh_max_i: decl("hsh_max_i", i64t.fn_type(&[i64t.into(), i64t.into()], false)),
            hsh_min_f: decl("hsh_min_f", f64t.fn_type(&[f64t.into(), f64t.into()], false)),
            hsh_max_f: decl("hsh_max_f", f64t.fn_type(&[f64t.into(), f64t.into()], false)),
            hsh_getcwd: np("hsh_getcwd"),
            hsh_chdir: pi("hsh_chdir"),
            hsh_username: np("hsh_username"),
            hsh_platform: np("hsh_platform"),
            hsh_setenv: ppi("hsh_setenv"),
            hsh_base64_encode: pp("hsh_base64_encode"),
            hsh_base64_decode: pp("hsh_base64_decode"),
            hsh_url_encode: pp("hsh_url_encode"),
            hsh_url_decode: pp("hsh_url_decode"),
            hsh_map_new:    ip("hsh_map_new"),
            hsh_map_set:    decl("hsh_map_set", void.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_map_get:    decl("hsh_map_get", i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_map_has:    decl("hsh_map_has", i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_map_remove: decl("hsh_map_remove", i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_map_len:    pi("hsh_map_len"),
            hsh_map_keys:   pp("hsh_map_keys"),
            hsh_map_clear:  decl("hsh_map_clear", void.fn_type(&[ptr.into()], false)),
            hsh_is_dir:        pi("hsh_is_dir"),
            hsh_is_file:       pi("hsh_is_file"),
            hsh_append_file:   ppi("hsh_append_file"),
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
            // Regex
            hsh_regex_match:   ppi("hsh_regex_match"),
            hsh_regex_find:    ppp("hsh_regex_find"),
            hsh_regex_replace: pppp("hsh_regex_replace"),
            // SQLite
            hsh_sqlite_open:        pp("hsh_sqlite_open"),
            hsh_sqlite_exec:        ppp("hsh_sqlite_exec"),
            hsh_sqlite_query:       ppp("hsh_sqlite_query"),
            hsh_sqlite_query_bind1: pppp("hsh_sqlite_query_bind1"),
            hsh_sqlite_query_bind2: p4("hsh_sqlite_query_bind2"),
            hsh_sqlite_query_bind3: p5("hsh_sqlite_query_bind3"),
            hsh_sqlite_close:       vp("hsh_sqlite_close"),
            // ── Dynamic arrays ────────────────────────────────────────────
            hsh_array_new:     np("hsh_array_new"),
            hsh_array_push:    decl("hsh_array_push", ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_array_len:     pi("hsh_array_len"),
            hsh_array_get:     decl("hsh_array_get",  i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_array_set:     decl("hsh_array_set",  ptr.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_array_concat:  ppp("hsh_array_concat"),
            hsh_array_contains: ppi("hsh_array_contains"),
            // env::args()
            hsh_env_args:      np("hsh_env_args"),
            // Struct helpers
            hsh_struct_new:    ip("hsh_struct_new"),
            hsh_struct_get:    decl("hsh_struct_get", i64t.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_struct_set:    decl("hsh_struct_set", ptr.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            // Extra string helpers
            hsh_string_split:  ppp("hsh_string_split"),
            hsh_string_find:   ppi("hsh_string_find"),
            hsh_string_rfind:  ppi("hsh_string_rfind"),
            hsh_string_slice:  decl("hsh_string_slice", ptr.fn_type(&[ptr.into(), i64t.into(), i64t.into()], false)),
            hsh_string_at:     decl("hsh_string_at",    ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_string_pad_right: decl("hsh_string_pad_right", ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_string_repeat: decl("hsh_string_repeat", ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_string_trim_right: pp("hsh_string_trim_right"),
            hsh_to_int:        pi("hsh_to_int"),
            hsh_to_int_from_hex: pi("hsh_to_int_from_hex"),
            hsh_to_float_fn:   decl("hsh_to_float", f64t.fn_type(&[ptr.into()], false)),
            hsh_proc_id:       ni("hsh_proc_id"),
            hsh_file_delete:   pi("hsh_file_delete"),
            hsh_dir_create:    pi("hsh_dir_create"),
            hsh_dir_exists:    pi("hsh_dir_exists"),
            // Extra aliases
            hsh_readline:        np("hsh_readline"),
            hsh_string_chars:    pp("hsh_string_chars"),
            hsh_dir_remove_all:  pi("hsh_dir_remove_all"),
            hsh_bytes_to_string: decl("hsh_bytes_to_string", ptr.fn_type(&[ptr.into(), i64t.into()], false)),
            hsh_string_to_bytes: pp("hsh_string_to_bytes"),
            hsh_string_contains: ppi("hsh_string_contains"),
            hsh_string_replace:  pppp("hsh_string_replace"),
            hsh_string_trim:     pp("hsh_string_trim"),
            hsh_string_upper:    pp("hsh_string_upper"),
            hsh_string_lower:    pp("hsh_string_lower"),
            hsh_string_starts_with: ppi("hsh_string_starts_with"),
            hsh_string_ends_with:   ppi("hsh_string_ends_with"),
            hsh_string_len:      pi("hsh_string_len"),
            hsh_array_remove:    decl("hsh_array_remove", i64t.fn_type(&[ptr.into(), i64t.into()], false)),
        }
    }
}
