package main

import "core:fmt"
import "core:os"
import "core:path/filepath"
import "core:strings"

main :: proc() {
    args := os.args[1:]
    if len(args) != 3 || args[1] != "-o" {
        fmt.eprintln("Usage: hsc <input.hs> -o <output.o>")
        os.exit(1)
    }

    input := args[0]
    output := args[2]

    // Get home dir
    home, ok := os.get_env("HOME")
    if !ok {
        home = "/home/default"
    }
    bin_path := filepath.join({home, ".hackeros", "H-Sharp"})
    parser_bin := filepath.join({bin_path, "h-sharp-parser"})
    compiler_bin := filepath.join({bin_path, "h-sharp-compiler"})

    // Create temp json file
    temp_dir := os.temp_dir()
    temp_json := filepath.join({temp_dir, "hsharp_temp.json"})
    defer os.remove(temp_json)

    // Run parser
    fmt.printf("Parsing %s...\n", input)
    parser_args := []string{input, temp_json}
    parser_exit_code := os.run_command(parser_bin, parser_args[:])
    if parser_exit_code != 0 {
        fmt.eprintln("Parser failed")
        os.exit(1)
    }

    // Run compiler
    fmt.println("Compiling...")
    compiler_args := []string{temp_json, output}
    compiler_exit_code := os.run_command(compiler_bin, compiler_args[:])
    if compiler_exit_code != 0 {
        fmt.eprintln("Compiler failed")
        os.exit(1)
    }

    fmt.printf("Compilation successful: %s\n", output)
}

// Note: This is a direct port from Rust to Odin.
// Assumptions:
// - os.run_command is used to execute external commands (Odin's os.exec or similar; adjust if needed).
// - filepath.join for paths.
// - os.temp_dir() exists or implement.
// - defer os.remove for cleanup.
// In real Odin, use core:os/exec for command execution if available.
// Odin stdlib has os.exec_cmd or similar in core:sys/unix or windows.
// This is simplified; adjust for platform-specific exec.
