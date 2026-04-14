use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::FunctionType;
use inkwell::values::FunctionValue;
use inkwell::AddressSpace;

pub struct LlvmBuiltins<'ctx> {
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
}

impl<'ctx> LlvmBuiltins<'ctx> {
    pub fn declare(ctx: &'ctx Context, module: &Module<'ctx>) -> Self {
        let i8_ptr = ctx.ptr_type(AddressSpace::default());
        let i64    = ctx.i64_type();
        let i32    = ctx.i32_type();
        let i8     = ctx.i8_type();
        let void   = ctx.void_type();

        let declare = |name: &str, fn_type: FunctionType<'ctx>| -> FunctionValue<'ctx> {
            module.get_function(name).unwrap_or_else(|| {
                module.add_function(name, fn_type, None)
            })
        };

        Self {
            hsh_println: declare("hsh_println",
                void.fn_type(&[i8_ptr.into()], false)),
            hsh_print: declare("hsh_print",
                void.fn_type(&[i8_ptr.into()], false)),
            hsh_panic: declare("hsh_panic",
                void.fn_type(&[i8_ptr.into()], false)),
            hsh_assert: declare("hsh_assert",
                void.fn_type(&[i8.into(), i8_ptr.into()], false)),
            hsh_int_to_string: declare("hsh_int_to_string",
                i8_ptr.fn_type(&[i64.into()], false)),
            hsh_strlen: declare("hsh_strlen",
                i64.fn_type(&[i8_ptr.into()], false)),
            hsh_strcat: declare("hsh_strcat",
                i8_ptr.fn_type(&[i8_ptr.into(), i8_ptr.into()], false)),
            exit_fn: declare("exit",
                void.fn_type(&[i32.into()], false)),
            malloc: declare("malloc",
                i8_ptr.fn_type(&[i64.into()], false)),
            free: declare("free",
                void.fn_type(&[i8_ptr.into()], false)),
        }
    }
}
