mod ast;
mod lexer;
mod parser;

use crate::ast::*;
use crate::lexer::{lexer, Span};
use crate::parser::parser;
use anyhow::{Context, Result};
use chumsky::prelude::*;
use chumsky::Stream;
use std::collections::HashSet;
use std::fs;
use std::hash::Hash;

fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: h-sharp-parser <input_source> <output_json>");
        std::process::exit(1);
    }
    let input_source = &args[1];
    let output_json = &args[2];
    let src = fs::read_to_string(input_source).context("Failed to read source file")?;

    // Lexer
    let tokens = lexer().parse(src.as_str()).map_err(|errs| {
        for err in errs {
            eprintln!("{}", error_message(&src, err.map(|c| c.to_string())));
        }
        anyhow::anyhow!("Lexer failed")
    })?;

    // Parser
    let len = src.chars().count();
    let (program, parse_errs) = parser().parse_recovery(Stream::from_iter(
        len..len + 1,
        tokens.into_iter(),
    ));

    if !parse_errs.is_empty() {
        for err in parse_errs {
            eprintln!("{}", error_message(&src, err));
        }
        return Err(anyhow::anyhow!("Parser failed"));
    }

    let mut program = program.context("No program parsed")?;
    let mut visited = HashSet::new();
    resolve_imports(&mut program, &mut visited, input_source)?;
    let json = serde_json::to_string(&program).context("Failed to serialize to JSON")?;
    fs::write(output_json, json).context("Failed to write output JSON")?;
    Ok(())
}

fn error_message<T: std::fmt::Debug + Hash + Eq>(src: &str, err: Simple<T, Span>) -> String {
    let span = err.span();
    let mut line = 1;
    let mut col = 1;
    let mut index = 0;
    for c in src.chars() {
        if index >= span.start {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
        index += c.len_utf8();
    }
    format!("Error at line {} column {}: {:?}", line, col, err)
}

fn resolve_imports(
    program: &mut HSharpProgram,
    visited: &mut HashSet<String>,
    _current_file: &str,
) -> Result<()> {
    let mut new_stmts = Vec::new();
    for stmt in program.stmts.drain(..) {
        if let HSharpStmt::Import(from, requires) = stmt {
            for require in requires {
                let (mod_name, opt_symbols) = match require {
                    RequireItem::WholeModule(m) => (m, None),
                    RequireItem::Specific(m, s) => (m, Some(vec![s])),
                };
                let file_path = format!("/usr/lib/H-Sharp/libs/{}/{}.h#", from, mod_name);
                if visited.contains(&file_path) {
                    return Err(anyhow::anyhow!("Cycle in imports: {}", file_path));
                }
                visited.insert(file_path.clone());
                let sub_src = fs::read_to_string(&file_path).unwrap_or_else(|_| {
                    eprintln!("Warning: Lib file {} not found", file_path);
                    String::new()
                });
                if sub_src.is_empty() {
                    continue;
                }

                // Lex Subfile
                let sub_tokens = lexer().parse(sub_src.as_str()).map_err(|errs| {
                    for err in errs {
                        eprintln!(
                            "Sub lexer error: {}",
                            error_message(&sub_src, err.map(|c| c.to_string()))
                        );
                    }
                    anyhow::anyhow!("Sub lexer failed")
                })?;

                // Parse Subfile
                let len = sub_src.chars().count();
                let (sub_program_opt, parse_errs) = parser().parse_recovery(Stream::from_iter(
                    len..len + 1,
                    sub_tokens.into_iter(),
                ));

                if !parse_errs.is_empty() {
                    for err in parse_errs {
                        eprintln!("Sub parse error: {}", error_message(&sub_src, err));
                    }
                    return Err(anyhow::anyhow!("Sub parser failed"));
                }

                let mut sub_program = sub_program_opt.context("No sub program parsed")?;
                resolve_imports(&mut sub_program, visited, &file_path)?;

                let added_stmts = if let Some(symbols) = opt_symbols {
                    sub_program
                    .stmts
                    .into_iter()
                    .filter(|stmt| match stmt {
                        HSharpStmt::FunctionDef(n, _, _, _) => symbols.contains(n),
                            HSharpStmt::StructDef(n, _) | HSharpStmt::UnionDef(n, _) => {
                                symbols.contains(n)
                            }
                            _ => false,
                    })
                    .collect::<Vec<_>>()
                } else {
                    sub_program.stmts
                };
                new_stmts.extend(added_stmts);
            }
        } else {
            new_stmts.push(stmt);
        }
    }
    program.stmts = new_stmts;
    Ok(())
}
