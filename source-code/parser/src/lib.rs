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
use std::path::{Path, PathBuf};

pub fn parse_code(src: &str, filename: &str) -> Result<HSharpProgram> {
    let (tokens, lex_errs) = lexer().parse_recovery(src);

    if !lex_errs.is_empty() {
        print_errors(
            src,
            filename,
            lex_errs
            .into_iter()
            .map(|e| e.map(|c| c.to_string()))
            .collect(),
        );
        return Err(anyhow::anyhow!("Lexer failed"));
    }
    let tokens = tokens.unwrap();

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

fn print_errors<T>(src: &str, filename: &str, errs: Vec<Simple<T>>)
where
T: std::fmt::Debug + std::fmt::Display + std::hash::Hash + Eq,
{
    for err in errs {
        let msg = if let Some(label) = err.label() {
            label.to_string()
        } else {
            match err.found() {
                Some(f) => format!("Unexpected token '{}'", f),
                None => "Unexpected end of file".to_string(),
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

fn find_library_path(lib_name: &str, mod_name: &str) -> Option<PathBuf> {
    let base_libs = Path::new("/usr/lib/h-sharp/libs");

    let direct_path = base_libs.join(lib_name).join(format!("{}.h#", mod_name));
    if direct_path.exists() {
        return Some(direct_path);
    }

    let envs_path = base_libs.join("envs");
    if let Ok(entries) = fs::read_dir(envs_path) {
        let mut paths: Vec<_> = entries
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .collect();
        paths.sort();

        for env_path in paths {
            if env_path.is_dir() {
                let direct_file = env_path.join(format!("{}.h#", lib_name));
                if direct_file.exists() && mod_name == lib_name {
                    return Some(direct_file);
                }

                let sub_dir_file = env_path.join(lib_name).join(format!("{}.h#", mod_name));
                if sub_dir_file.exists() {
                    return Some(sub_dir_file);
                }
            }
        }
    }

    None
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

                let file_path_buf = find_library_path(&from, &mod_name).ok_or_else(|| {
                    anyhow::anyhow!(
                        "Library not found: {}/{}. Please install it using 'h# install {}'",
                        from,
                        mod_name,
                        from
                    )
                })?;

                let file_path = file_path_buf.to_string_lossy().to_string();

                if visited.contains(&file_path) {
                    return Err(anyhow::anyhow!("Cycle in imports: {}", file_path));
                }
                visited.insert(file_path.clone());

                let sub_src = fs::read_to_string(&file_path).unwrap_or_default();
                if sub_src.is_empty() {
                    continue;
                }

                let (tokens, _) = lexer().parse_recovery(sub_src.as_str());
                if let Some(toks) = tokens {
                    let len = sub_src.chars().count();
                    let (sub_prog, _) = parser().parse_recovery(Stream::from_iter(
                        len..len + 1,
                        toks.into_iter(),
                    ));
                    if let Some(mut sp) = sub_prog {
                        resolve_imports(&mut sp, visited, &file_path)?;
                        if let Some(symbols) = opt_symbols {
                            let added = sp
                            .stmts
                            .into_iter()
                            .filter(|s| match s {
                                HSharpStmt::FunctionDef(n, ..)
                                | HSharpStmt::StructDef(n, ..)
                                | HSharpStmt::UnionDef(n, ..) => symbols.contains(n),
                                    _ => false,
                            })
                            .collect::<Vec<_>>();
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
