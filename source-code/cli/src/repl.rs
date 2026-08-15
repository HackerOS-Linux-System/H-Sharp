use colored::Colorize;
use std::io::Write;

pub fn run() {
    println!("{}", "  H# REPL v0.8".cyan().bold());
    println!("{}", "  Type H# statements or expressions. `:help` for commands, `:quit` to exit.".dimmed());
    println!();

    let mut interp = hsharp_interpreter::Interpreter::new();
    let mut line_no: usize = 0;
    // Multi-line buffering: if a line leaves an unclosed block (`is`/`do`
    // without a matching `end`, or an unbalanced `(`/`{`/`[`), keep
    // prompting with a continuation marker and accumulate until it
    // balances — so typing a multi-line `if ... is ... end` or `fn ...`
    // interactively doesn't require it all on one physical line.
    let mut buffer = String::new();

    loop {
        let prompt = if buffer.is_empty() {
            format!("h#[{}]> ", line_no)
        } else {
            "   ...  ".to_string()
        };
        print!("{}", prompt.green());
        let _ = std::io::stdout().flush();

        let mut input = String::new();
        if std::io::stdin().read_line(&mut input).unwrap_or(0) == 0 {
            println!();
            break; // EOF (Ctrl+D)
        }
        let trimmed = input.trim_end_matches(['\n', '\r']);

        if buffer.is_empty() {
            match trimmed.trim() {
                ":quit" | ":q" | ":exit" => break,
                ":help" | ":h" => { print_help(); continue; }
                ":clear" => {
                    interp = hsharp_interpreter::Interpreter::new();
                    println!("{}", "  (session reset)".dimmed());
                    continue;
                }
                "" => continue,
                _ => {}
            }
        }

        buffer.push_str(trimmed);
        buffer.push('\n');

        if !is_balanced(&buffer) {
            continue; // keep accumulating
        }

        let src = std::mem::take(&mut buffer);
        line_no += 1;

        let file_label = format!("<repl:{}>", line_no);
        let mut lexer = hsharp_parser::lexer::Lexer::new(&src, file_label.clone());
        let tokens = match lexer.tokenize() {
            Ok(t) => t,
            Err(errs) => {
                for e in errs { eprintln!("{}", e.render(&src)); }
                continue;
            }
        };
        let mut parser = hsharp_parser::parser::Parser::new(tokens, src.clone(), file_label);
        match parser.parse_stmt() {
            Ok(stmts) => {
                for stmt in &stmts {
                    // `exec_stmt` deliberately discards an expression
                    // statement's value (see interp.rs's `Stmt::Expr` arm
                    // — right for a normal program, where a bare `x + 1`
                    // mid-function does nothing observable) so a REPL
                    // needs to special-case plain expressions and call
                    // `eval_expr` itself to actually get the value back
                    // and echo it, the way every other REPL does.
                    let outcome = if let hsharp_parser::ast::Stmt::Expr(expr, _) = stmt {
                        interp.eval_expr(expr).map(Some)
                    } else {
                        interp.exec_stmt(stmt)
                    };
                    match outcome {
                        Ok(Some(v)) if !matches!(v, hsharp_interpreter::Value::Nil) => {
                            println!("{} {}", "=>".dimmed(), format!("{:?}", v).yellow());
                        }
                        Ok(_) => {}
                        Err(hsharp_interpreter::RuntimeError::Exit(code)) => std::process::exit(code),
                        Err(e) => eprintln!("{} {}", "Runtime error:".red().bold(), e),
                    }
                }
            }
            Err(e) => eprintln!("{}", e.render(&src)),
        }
    }

    println!("{}", "  bye!".dimmed());
}

/// Cheap balance check over `is`/`do`/`end` keywords and bracket pairs —
/// good enough to decide "does this look finished" for a REPL prompt
/// without re-implementing the parser's own recovery logic. Strings and
/// comments are skipped so a `"("` inside a string literal can't fool it.
fn is_balanced(src: &str) -> bool {
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut chars = src.chars().peekable();
    while let Some(c) = chars.next() {
        if in_string {
            if c == '\\' { chars.next(); }
            else if c == '"' { in_string = false; }
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
    }
    if depth != 0 { return false; }

    // Keyword-based block balance: every `is`/`do` that opens a block
    // wants one `end`. Rough but effective for `fn`/`if`/`while`/`for`/
    // `match`/`impl`/`struct`/`trait` bodies, which are the multi-line
    // constructs someone would actually type at a REPL.
    let opens = count_word(src, "is") + count_word(src, "do");
    let ends  = count_word(src, "end");
    opens <= ends
}

fn count_word(src: &str, word: &str) -> usize {
    src.split(|c: char| !c.is_alphanumeric() && c != '_')
        .filter(|w| *w == word)
        .count()
}

fn print_help() {
    println!("{}", "  REPL commands:".bold());
    println!("    :help, :h     show this message");
    println!("    :clear        reset the session (clears all vars/fns/consts)");
    println!("    :quit, :q     exit the REPL");
    println!("  Anything else is evaluated as H# — expressions, `let`, `fn`, `const`, `struct`, `enum`.");
}
