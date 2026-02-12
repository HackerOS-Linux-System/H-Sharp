pub mod ast;
pub mod lexer;
pub mod parser;

use crate::ast::*;
use crate::lexer::lexer;
use crate::parser::parser;
use anyhow::{Context, Result};
use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::*;
use chumsky::Stream;
use std::collections::HashSet;
use std::fs;

pub fn parse_code(src: &str, filename: &str) -> Result<HSharpProgram> {
    // Lexer
    let (tokens, lex_errs) = lexer().parse_recovery(src);

    if !lex_errs.is_empty() {
        print_errors(src, filename, lex_errs.into_iter().map(|e| e.map(|c| c.to_string())).collect());
        return Err(anyhow::anyhow!("Lexer failed"));
    }
    let tokens = tokens.unwrap();

    // Parser
    let len = src.chars().count();
    let (program, parse_errs) = parser().parse_recovery(Stream::from_iter(
        len..len + 1,
        tokens.into_iter(),
    ));

    if !parse_errs.is_empty() {
        print_errors(src, filename, parse_errs);
        return Err(anyhow::anyhow!("Parser failed"));
    }

    let mut program = program.context("No program parsed")?;
    let mut visited = HashSet::new();
    resolve_imports(&mut program, &mut visited, filename)?;
    Ok(program)
}

fn print_errors<T: std::fmt::Debug + std::fmt::Display + std::hash::Hash + std::cmp::Eq>(src: &str, filename: &str, errs: Vec<Simple<T>>) {
    for err in errs {
        let msg = if let Some(label) = err.label() {
            label.to_string()
        } else {
            match err.found() {
                Some(f) => format!("Unexpected token '{}'", f),
                None => "Unexpected end of file".to_string()
            }
        };

        let report = Report::build(ReportKind::Error, filename, err.span().start)
        .with_message("Parse Error")
        .with_label(
            Label::new((filename, err.span()))
            .with_message(msg)
            .with_color(Color::Red),
        );

        let _ = report.finish().print((filename, Source::from(src)));
    }
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
                let sub_src = fs::read_to_string(&file_path).unwrap_or_else(|_| String::new());
                if sub_src.is_empty() { continue; }

                let (tokens, _) = lexer().parse_recovery(sub_src.as_str());
                if let Some(toks) = tokens {
                    let len = sub_src.chars().count();
                    let (sub_prog, _) = parser().parse_recovery(Stream::from_iter(len..len+1, toks.into_iter()));
                    if let Some(mut sp) = sub_prog {
                        resolve_imports(&mut sp, visited, &file_path)?;
                        if let Some(symbols) = opt_symbols {
                            let added = sp.stmts.into_iter().filter(|s| match s {
                                HSharpStmt::FunctionDef(n, ..) | HSharpStmt::StructDef(n, ..) | HSharpStmt::UnionDef(n, ..) => symbols.contains(n),
                                                                    _ => false
                            }).collect::<Vec<_>>();
                            new_stmts.extend(added);
                        } else {
                            new_stmts.extend(sp.stmts);
                        }
                    }
                }
            }
        } else {
            new_stmts.push(stmt);
        }
    }
    program.stmts = new_stmts;
    Ok(())
}
