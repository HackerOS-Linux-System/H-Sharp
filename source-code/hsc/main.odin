package main

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:strings"
import "core:c/libc"

run_command :: proc(bin: string, args: []string) -> int {
    sb := strings.builder_make(context.temp_allocator)
    defer strings.builder_destroy(&sb)
    strings.write_string(&sb, bin)
    for arg in args {
        strings.write_rune(&sb, ' ')
        // Simple quoting if arg has space
        if strings.contains(arg, " ") {
            strings.write_rune(&sb, '"')
            strings.write_string(&sb, arg)
            strings.write_rune(&sb, '"')
        } else {
            strings.write_string(&sb, arg)
        }
    }
    cmd_str := strings.to_string(sb)
    c_cmd := strings.clone_to_cstring(cmd_str, context.temp_allocator)
    defer delete(c_cmd)
    res := libc.system(c_cmd)
    if res == -1 {
        return 1
    }
    return int((res >> 8) & 0xff)
}

temp_dir :: proc() -> string {
    dir := os.get_env("TMPDIR")
    if dir != "" {
        return dir
    }
    return "/tmp"
}

main :: proc() {
    args := os.args[1:]
    if len(args) != 3 || args[1] != "-o" {
        fmt.eprintln("Usage: hsc <input.hs> -o <output.o>")
        os.exit(1)
    }
    input := args[0]
    output := args[2]
    // Get home dir
    home := os.get_env("HOME")
    if home == "" {
        home = "/home/default"
    }
    bin_path, _ := filepath.join([]string{home, ".hackeros", "H-Sharp"})
    parser_bin, _ := filepath.join([]string{bin_path, "h-sharp-parser"})
    compiler_bin, _ := filepath.join([]string{bin_path, "h-sharp-compiler"})
    // Create temp json file
    temp_dir_path := temp_dir()
    temp_json, _ := filepath.join([]string{temp_dir_path, "hsharp_temp.json"})
    defer os.remove(temp_json)
    // Run parser
    fmt.printf("Parsing %s...\n", input)
    parser_args := []string{input, temp_json}
    parser_exit_code := run_command(parser_bin, parser_args)
    if parser_exit_code != 0 {
        fmt.eprintln("Parser failed")
        os.exit(1)
    }
    // Run compiler
    fmt.println("Compiling...")
    compiler_args := []string{temp_json, output}
    compiler_exit_code := run_command(compiler_bin, compiler_args)
    if compiler_exit_code != 0 {
        fmt.eprintln("Compiler failed")
        os.exit(1)
    }
    fmt.printf("Compilation successful: %s\n", output)
}
