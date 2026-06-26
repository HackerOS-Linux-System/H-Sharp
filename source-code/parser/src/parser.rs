use crate::ast::*;
use crate::error::{ParseError, ParseErrorKind, ErrorReporter};
use crate::lexer::{Token, TokenKind};
use crate::span::Span;

pub struct Parser {
    tokens: Vec<Token>,
    pos:    usize,
    #[allow(dead_code)] source: String,
    file:   String,
    pub errors: ErrorReporter,
}

#[allow(dead_code)]
impl Parser {
    pub fn new(tokens: Vec<Token>, source: String, file: String) -> Self {
        Self { tokens, pos: 0, source, file, errors: ErrorReporter::new() }
    }

    // ── Token navigation ──────────────────────────────────────────────────────

    fn current(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or_else(|| self.tokens.last().unwrap())
    }

    fn peek_at(&self, offset: usize) -> &Token {
        self.tokens.get(self.pos + offset).unwrap_or_else(|| self.tokens.last().unwrap())
    }

    fn advance(&mut self) -> &Token {
        let t = &self.tokens[self.pos];
        if self.pos < self.tokens.len() - 1 { self.pos += 1; }
        t
    }

    fn skip_newlines(&mut self) {
        while matches!(self.current().kind, TokenKind::Newline) { self.advance(); }
    }

    fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current().kind) == std::mem::discriminant(kind)
    }

    fn expect(&mut self, kind: &TokenKind) -> Result<Token, ParseError> {
        if std::mem::discriminant(&self.current().kind) == std::mem::discriminant(kind) {
            Ok(self.advance().clone())
        } else {
            Err(ParseError::new(
                ParseErrorKind::ExpectedToken(format!("{:?}", kind)),
                                self.current().span.clone(),
                                format!("expected `{}`, found `{}`", token_kind_name(kind), self.current().text),
                                    vec![format!("add `{}` here", token_kind_name(kind))],
            ))
        }
    }

    fn expect_ident(&mut self) -> Result<(String, Span), ParseError> {
        if let TokenKind::Ident(name) = &self.current().kind {
            let name = name.clone();
            let span = self.current().span.clone();
            self.advance();
            Ok((name, span))
        } else {
            Err(ParseError::new(
                ParseErrorKind::ExpectedIdent,
                self.current().span.clone(),
                                format!("expected identifier, found `{}`", self.current().text),
                                    vec!["provide a valid identifier here".to_string()],
            ))
        }
    }

    /// Like `expect_ident`, but also accepts a fixed set of "soft" keywords
    /// that are reserved words in statement/type position but are extremely
    /// common as method or path-segment names in real-world APIs — most
    /// importantly `new` (`Type::new()`) and `write` (`module::write()`).
    /// Without this, `col::HashMap::new()` or `fs::write(...)` fail to
    /// parse with a confusing "expected identifier, found `new`" error,
    /// even though `new`/`write` are perfectly unambiguous in path-segment
    /// position (they can never start a path segment themselves, so there's
    /// no grammar conflict in allowing them here).
    fn expect_path_segment(&mut self) -> Result<(String, Span), ParseError> {
        let span = self.current().span.clone();
        let text = match &self.current().kind {
            TokenKind::Ident(name) => Some(name.clone()),
            TokenKind::New      => Some("new".to_string()),
            TokenKind::Write    => Some("write".to_string()),
            TokenKind::Type     => Some("type".to_string()),
            TokenKind::End      => Some("end".to_string()),
            TokenKind::As       => Some("as".to_string()),
            TokenKind::Is       => Some("is".to_string()),
            TokenKind::From     => Some("from".to_string()),
            TokenKind::Use      => Some("use".to_string()),
            TokenKind::Match    => Some("match".to_string()),
            TokenKind::In       => Some("in".to_string()),
            TokenKind::For      => Some("for".to_string()),
            TokenKind::Mod      => Some("mod".to_string()),
            TokenKind::Async    => Some("async".to_string()),
            TokenKind::Await    => Some("await".to_string()),
            TokenKind::Self_    => Some("self".to_string()),
            _ => None,
        };
        match text {
            Some(name) => { self.advance(); Ok((name, span)) }
            None => Err(ParseError::new(
                ParseErrorKind::ExpectedIdent,
                span,
                format!("expected identifier, found `{}`", self.current().text),
                vec!["provide a valid identifier here".to_string()],
            )),
        }
    }

    fn error(&self, msg: impl Into<String>, hints: Vec<String>) -> ParseError {
        let msg_str: String = msg.into();
        ParseError::new(
            ParseErrorKind::Custom(msg_str.clone()),
                        self.current().span.clone(),
                        msg_str,
                        hints,
        )
    }

    fn recover(&mut self) {
        // Always consume at least one token before checking the stop
        // condition. Without this, an error that leaves the cursor sitting
        // exactly on a stop-token (e.g. `Fn`) makes recover() a no-op —
        // the caller's retry loop then sees the identical token again,
        // fails the identical way, calls recover() again, and never makes
        // progress. This was the root cause of a real hang (see the
        // TokenKind::Fn case in parse_type_base for the original trigger);
        // advancing unconditionally here makes recovery robust against
        // this whole class of stuck-cursor bugs, not just the one trigger
        // that's now also fixed at the source.
        if !matches!(self.current().kind, TokenKind::EOF) {
            self.advance();
        }
        while !matches!(self.current().kind,
            TokenKind::EOF | TokenKind::Newline | TokenKind::Fn | TokenKind::Struct |
            TokenKind::Enum | TokenKind::Impl | TokenKind::Pub | TokenKind::Use |
            TokenKind::End)
        {
            self.advance();
        }
    }

    // ── Module ─────────────────────────────────────────────────────────────────

    pub fn parse_module(&mut self) -> Module {
        let mut directives = Vec::new();
        let mut items      = Vec::new();
        let mut imports    = Vec::new();
        let mut edition: Option<String> = None;

        self.skip_newlines();

        while !matches!(self.current().kind, TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::EOF) { break; }

            // `using "2026"` edition declaration
            if matches!(self.current().kind, TokenKind::Using) {
                self.advance();
                if let TokenKind::StringLit(ed) = &self.current().kind.clone() {
                    edition = Some(ed.clone());
                    self.advance();
                }
                self.skip_newlines();
                continue;
            }

            // Directives ~ / ~~
            if let TokenKind::Directive(s) = &self.current().kind.clone() {
                let span = self.current().span.clone(); let s = s.clone(); self.advance();
                directives.push(Directive { kind: DirectiveKind::Dynamic, value: s, span });
                continue;
            }
            if let TokenKind::FastDirective(s) = &self.current().kind.clone() {
                let span = self.current().span.clone(); let s = s.clone(); self.advance();
                directives.push(Directive { kind: DirectiveKind::Fast, value: s, span });
                continue;
            }

            // `use` imports
            if matches!(self.current().kind, TokenKind::Use) {
                match self.parse_import() {
                    Ok((kind, alias, span)) => imports.push((kind, alias, span)),
                    Err(e) => { self.errors.report(e); self.recover(); }
                }
                continue;
            }

            // Top-level items
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(e)   => { self.errors.report(e); self.recover(); }
            }
        }

        Module { file: self.file.clone(), edition, directives, items, imports }
    }

    // ── Import ────────────────────────────────────────────────────────────────

    fn parse_import(&mut self) -> Result<(ImportKind, Option<String>, Span), ParseError> {
        let start = self.current().span.clone();
        self.advance(); // consume 'use'

        let path_tok = if let TokenKind::StringLit(s) = &self.current().kind.clone() {
            let s = s.clone(); self.advance(); s
        } else {
            return Err(self.error("expected use path string after `use`",
                                  vec![r#"write: use "std -> io" from "io""#.to_string()]));
        };

        let alias = if matches!(self.current().kind, TokenKind::From) {
            self.advance();
            if let TokenKind::StringLit(a) = &self.current().kind.clone() {
                let a = a.clone(); self.advance(); Some(a)
            } else {
                return Err(self.error("expected alias string after `from`", vec![]));
            }
        } else { None };

        let span = start.merge(&self.current().span);
        let kind = parse_use_path(&path_tok, alias.clone())
        .ok_or_else(|| ParseError::new(
            ParseErrorKind::Custom("invalid use path".into()),
                                       span.clone(),
                                       format!("cannot parse use path `{}`", path_tok),
                                           vec![r#"valid forms: "std -> module", "vira -> pkg/1.0""#.to_string()],
        ))?;
        Ok((kind, alias, span))
    }

    // ── Attributes ────────────────────────────────────────────────────────────

    fn parse_attributes(&mut self) -> Vec<Attribute> {
        let mut attrs = Vec::new();
        while matches!(self.current().kind, TokenKind::Hash) {
            let span = self.current().span.clone();
            self.advance(); // #
            if !matches!(self.current().kind, TokenKind::LBracket) { break; }
            self.advance(); // [
            let (name, _) = self.expect_ident().unwrap_or_else(|_| (String::new(), self.current().span.clone()));
            let mut args = Vec::new();
            if matches!(self.current().kind, TokenKind::LParen) {
                self.advance(); // (
                    while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                        let (k, _) = self.expect_ident().unwrap_or_else(|_| (String::new(), self.current().span.clone()));
                        if matches!(self.current().kind, TokenKind::Assign) {
                            self.advance();
                            let v = if let TokenKind::StringLit(s) = &self.current().kind.clone() {
                                let s = s.clone(); self.advance(); s
                            } else { String::new() };
                            args.push(AttrArg::KeyValue(k, v));
                        } else {
                            args.push(AttrArg::Ident(k));
                        }
                        if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                    }
                    if matches!(self.current().kind, TokenKind::RParen) { self.advance(); }
            }
            if matches!(self.current().kind, TokenKind::RBracket) { self.advance(); }
            let end_span = self.current().span.clone();
            attrs.push(Attribute { name, args, span: span.merge(&end_span) });
            self.skip_newlines();
        }
        attrs
    }

    // ── Items ─────────────────────────────────────────────────────────────────

    fn parse_item(&mut self) -> Result<Item, ParseError> {
        self.skip_newlines();
        let attrs = self.parse_attributes();
        let pub_ = if matches!(self.current().kind, TokenKind::Pub) {
            self.advance(); true
        } else { false };

        match &self.current().kind {
            TokenKind::Fn     => self.parse_fn_with_attrs(pub_, attrs).map(Item::FnDef),
            TokenKind::Struct => self.parse_struct(pub_).map(Item::StructDef),
            TokenKind::Enum   => self.parse_enum(pub_).map(Item::EnumDef),
            TokenKind::Trait  => self.parse_trait(pub_).map(Item::TraitDef),
            TokenKind::Impl   => self.parse_impl().map(Item::ImplBlock),
            TokenKind::Type   => self.parse_type_alias(pub_),
            TokenKind::Async  => {
                self.advance();
                let fn_def = self.parse_fn_with_attrs(pub_, attrs)?;
                Ok(Item::FnDef(FnDef { is_async: true, ..fn_def }))
            }
            TokenKind::Mod    => self.parse_mod_decl(pub_),
            TokenKind::Extern => self.parse_extern_block_inline(),
            TokenKind::Using  => {
                self.advance();
                if let TokenKind::StringLit(_) = &self.current().kind.clone() { self.advance(); }
                self.skip_newlines();
                self.parse_item()
            }
            _ => Err(self.error(
                format!("unexpected token `{}` at top level", self.current().text),
                    vec!["expected fn, struct, enum, trait, impl, type, mod, or extern".to_string()],
            )),
        }
    }

    fn parse_mod_decl(&mut self, pub_: bool) -> Result<Item, ParseError> {
        let span = self.current().span.clone();
        self.advance(); // mod
        let (name, _) = self.expect_ident()?;
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance(); self.skip_newlines();
            let mut inner = Vec::new();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End | TokenKind::EOF) { break; }
                match self.parse_item() {
                    Ok(i)  => inner.push(i),
                    Err(e) => { self.errors.report(e); self.recover(); }
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
            let end = self.current().span.clone();
            Ok(Item::ModDecl { name, pub_, inline: Some(inner), span: span.merge(&end) })
        } else {
            let end = self.current().span.clone();
            Ok(Item::ModDecl { name, pub_, inline: None, span: span.merge(&end) })
        }
    }

    fn parse_fn(&mut self, pub_: bool) -> Result<FnDef, ParseError> {
        self.parse_fn_with_attrs(pub_, vec![])
    }

    fn parse_fn_with_attrs(&mut self, pub_: bool, attrs: Vec<Attribute>) -> Result<FnDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // fn
        let is_async  = if matches!(self.current().kind, TokenKind::Async)  { self.advance(); true } else { false };
        let is_unsafe = if matches!(self.current().kind, TokenKind::Unsafe) { self.advance(); true } else { false };
        // Use expect_path_segment (not expect_ident) here: `new` and `write`
        // are reserved keyword tokens but are also extremely common
        // function/method names (`fn new(...)`, constructor-style; `fn
        // write(...)`, e.g. inside `impl Buffer`). They're unambiguous in
        // this position — nothing else can follow `fn` here — so accepting
        // them avoids a confusing "expected identifier, found `new`" error
        // on otherwise completely ordinary code (see tests/core/types_test.h#'s
        // `impl Point is fn new(x, y) -> Point ... end end`).
        let (name, _) = self.expect_path_segment()?;
        let type_params = self.parse_generics_decl()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;
        let return_type = if matches!(self.current().kind, TokenKind::Arrow) {
            self.advance(); Some(self.parse_type()?)
        } else { None };
        self.skip_newlines();
        let body = self.parse_block()?;
        let span = start.merge(&self.current().span);
        Ok(FnDef { attrs, type_params, name, params, return_type, body, pub_, is_async, is_unsafe, span })
    }

    fn parse_params(&mut self) -> Result<Vec<Param>, ParseError> {
        let mut params = Vec::new();
        while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::RParen) { break; }
            let span    = self.current().span.clone();
            let mutable = if matches!(self.current().kind, TokenKind::Mut) { self.advance(); true } else { false };
            if matches!(self.current().kind, TokenKind::Self_) {
                let s = self.advance().span.clone();
                params.push(Param { name: "self".to_string(), ty: TypeExpr::Named("Self".to_string()), mutable, span: s });
            } else {
                let (name, _) = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type()?;
                params.push(Param { name, ty, mutable, span });
            }
            if matches!(self.current().kind, TokenKind::Comma) { self.advance(); } else { break; }
        }
        Ok(params)
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.skip_newlines();
        let mut stmts = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance(); self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End | TokenKind::EOF) { break; }
                match self.parse_stmt() {
                    Ok(s)  => stmts.extend(s),
                    Err(e) => { self.errors.report(e); self.recover(); }
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        } else if matches!(self.current().kind, TokenKind::Assign) {
            self.advance();
            let expr = self.parse_expr(0)?;
            let span = expr.span().clone();
            stmts.push(Stmt::Return(Some(expr), span));
        } else {
            return Err(self.error(
                "expected `is` to start a block body",
                vec!["write `is` before the body and `end` after".to_string()],
            ));
        }
        Ok(stmts)
    }

    /// Parse an if-branch body — stops at else/elsif/end without consuming them
    fn parse_if_body(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.skip_newlines();
        // Must start with `is`
        if !matches!(self.current().kind, TokenKind::Is) {
            return Err(self.error(
                "expected `is` after condition",
                vec!["write: if cond is ... end".to_string()],
            ));
        }
        self.advance(); // consume `is`
        self.skip_newlines();

        let mut stmts = Vec::new();
        loop {
            self.skip_newlines();
            match self.current().kind {
                TokenKind::End | TokenKind::EOF => break,
                TokenKind::Else | TokenKind::Elsif => break,
                _ => {}
            }
            match self.parse_stmt() {
                Ok(s)  => stmts.extend(s),
                Err(e) => { self.errors.report(e); self.recover(); }
            }
        }
        // Only consume `end` if there is no else/elsif following
        if matches!(self.current().kind, TokenKind::End) {
            self.advance();
        }
        Ok(stmts)
    }

    fn parse_struct(&mut self, pub_: bool) -> Result<StructDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // struct
        let (name, _) = self.expect_ident()?;
        let type_params = self.parse_generics_decl()?;
        self.skip_newlines();
        let mut fields = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance(); self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End) { break; }
                let fpub = if matches!(self.current().kind, TokenKind::Pub) { self.advance(); true } else { false };
                let fspan = self.current().span.clone();
                let (fname, _) = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                let fty = self.parse_type()?;
                fields.push(StructField { name: fname, ty: fty, pub_: fpub, span: fspan });
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        }
        let span = start.merge(&self.current().span);
        Ok(StructDef { attrs: vec![], type_params, name, fields, pub_, span })
    }

    fn parse_enum(&mut self, pub_: bool) -> Result<EnumDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // enum
        let (name, _) = self.expect_ident()?;
        let type_params = self.parse_generics_decl()?;
        self.skip_newlines();
        let mut variants = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance(); self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End) { break; }
                let vspan = self.current().span.clone();
                let (vname, _) = self.expect_ident()?;
                let fields = if matches!(self.current().kind, TokenKind::LParen) {
                    self.advance();
                    let mut types = Vec::new();
                    while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                        types.push(self.parse_type()?);
                        if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                    }
                    self.expect(&TokenKind::RParen)?;
                    EnumVariantFields::Tuple(types)
                } else if matches!(self.current().kind, TokenKind::Is) {
                    // Struct variant: Variant is field: T ... end
                    self.advance(); self.skip_newlines();
                    let mut sfields = Vec::new();
                    while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                        self.skip_newlines();
                        if matches!(self.current().kind, TokenKind::End) { break; }
                        let fpub = if matches!(self.current().kind, TokenKind::Pub) { self.advance(); true } else { false };
                        let fs = self.current().span.clone();
                        let (fn_, _) = self.expect_ident()?;
                        self.expect(&TokenKind::Colon)?;
                        let ft = self.parse_type()?;
                        sfields.push(StructField { name: fn_, ty: ft, pub_: fpub, span: fs });
                        self.skip_newlines();
                    }
                    self.expect(&TokenKind::End)?;
                    EnumVariantFields::Struct(sfields)
                } else {
                    EnumVariantFields::Unit
                };
                variants.push(EnumVariant { name: vname, fields, span: vspan });
                if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        }
        let span = start.merge(&self.current().span);
        Ok(EnumDef { attrs: vec![], type_params, name, variants, pub_, span })
    }

    fn parse_trait(&mut self, pub_: bool) -> Result<TraitDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // trait
        let (name, _) = self.expect_ident()?;
        self.skip_newlines();
        let mut methods = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance(); self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End) { break; }
                if matches!(self.current().kind, TokenKind::Fn) {
                    self.advance();
                    let mspan = self.current().span.clone();
                    let (mname, _) = self.expect_ident()?;
                    self.expect(&TokenKind::LParen)?;
                    let params = self.parse_params()?;
                    self.expect(&TokenKind::RParen)?;
                    let ret = if matches!(self.current().kind, TokenKind::Arrow) {
                        self.advance(); Some(self.parse_type()?)
                    } else { None };
                    self.skip_newlines();
                    let default_body = if matches!(self.current().kind, TokenKind::Is) {
                        Some(self.parse_block()?)
                    } else { None };
                    methods.push(TraitMethod { name: mname, params, return_type: ret, default_body, span: mspan });
                } else {
                    let e = self.error("expected `fn` in trait", vec![]);
                    self.errors.report(e); self.recover();
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        }
        let span = start.merge(&self.current().span);
        Ok(TraitDef { attrs: vec![], type_params: vec![], name, methods, pub_, span })
    }

    fn parse_impl(&mut self) -> Result<ImplBlock, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // impl
        let (type_name, _) = self.expect_ident()?;
        let trait_name = if matches!(self.current().kind, TokenKind::Colon) {
            self.advance(); let (t, _) = self.expect_ident()?; Some(t)
        } else { None };
        self.skip_newlines();
        let mut methods = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance(); self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End) { break; }
                let pub_ = if matches!(self.current().kind, TokenKind::Pub) { self.advance(); true } else { false };
                if matches!(self.current().kind, TokenKind::Fn) {
                    match self.parse_fn(pub_) {
                        Ok(f)  => methods.push(f),
                        Err(e) => { self.errors.report(e); self.recover(); }
                    }
                } else {
                    let e = self.error("expected `fn` in impl block", vec![]);
                    self.errors.report(e); self.recover();
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        }
        let span = start.merge(&self.current().span);
        Ok(ImplBlock { type_name, trait_name, methods, span })
    }

    fn parse_type_alias(&mut self, pub_: bool) -> Result<Item, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // type
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;
        let span = start.merge(&self.current().span);
        Ok(Item::TypeAlias { name, ty, pub_, span })
    }

    fn parse_extern_block_inline(&mut self) -> Result<Item, ParseError> {
        let span = self.current().span.clone();
        self.advance(); // extern
        let link_kind = {
            let kw = if let TokenKind::Ident(ref s) = self.current().kind { s.clone() } else { String::new() };
            match kw.as_str() {
                "static"  => { self.advance(); ExternLinkKind::Static }
                "dynamic" => { self.advance(); ExternLinkKind::Dynamic }
                _         => ExternLinkKind::Static,
            }
        };
        let mut lang    = ExternLang::C;
        let mut library = None;
        if matches!(self.current().kind, TokenKind::LBracket) {
            self.advance();
            let s = if let TokenKind::Ident(ref ss) = self.current().kind { ss.clone() } else { String::new() };
            lang = match s.as_str() {
                "rust" | "Rust"     => ExternLang::Rust,
                "cpp" | "c++"       => ExternLang::Cpp,
                "python" | "py"     => ExternLang::Python,
                _                   => ExternLang::C,
            };
            self.advance();
            if matches!(self.current().kind, TokenKind::Comma) {
                self.advance();
                if let TokenKind::StringLit(s) = &self.current().kind.clone() { library = Some(s.clone()); self.advance(); }
            }
            if matches!(self.current().kind, TokenKind::RBracket) { self.advance(); }
        }
        self.skip_newlines();
        if matches!(self.current().kind, TokenKind::Is) { self.advance(); }
        self.skip_newlines();
        let mut functions = Vec::new();
        while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::End | TokenKind::EOF) { break; }
            if matches!(self.current().kind, TokenKind::Fn) {
                self.advance();
                let fspan = self.current().span.clone();
                let (name, _) = self.expect_ident()?;
                self.expect(&TokenKind::LParen)?;
                let mut params   = Vec::new();
                let mut variadic = false;
                while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                    if matches!(self.current().kind, TokenKind::DotDot) { variadic = true; self.advance(); break; }
                    let (pname, _) = self.expect_ident()?;
                    self.expect(&TokenKind::Colon)?;
                    let ty = self.parse_type()?;
                    params.push(Param { name: pname, ty, mutable: false, span: fspan.clone() });
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                }
                self.expect(&TokenKind::RParen)?;
                let ret = if matches!(self.current().kind, TokenKind::Arrow) { self.advance(); Some(self.parse_type()?) } else { None };
                functions.push(ExternFnDecl { name, params, return_type: ret, variadic, span: fspan });
            }
            self.skip_newlines();
        }
        self.expect(&TokenKind::End)?;
        Ok(Item::Extern(ExternBlock { lang, link_kind, library, functions, span }))
    }

    fn parse_generics_decl(&mut self) -> Result<Vec<TypeParam>, ParseError> {
        let mut params = Vec::new();
        if matches!(self.current().kind, TokenKind::Lt) {
            self.advance();
            while !matches!(self.current().kind, TokenKind::Gt | TokenKind::EOF) {
                let span = self.current().span.clone();
                let (name, _) = self.expect_ident()?;
                let mut bounds = Vec::new();
                if matches!(self.current().kind, TokenKind::Colon) {
                    self.advance();
                    loop {
                        let (bound, _) = self.expect_ident()?;
                        bounds.push(bound);
                        if matches!(self.current().kind, TokenKind::Plus) { self.advance(); } else { break; }
                    }
                }
                params.push(TypeParam { name, bounds, span });
                if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
            }
            self.expect(&TokenKind::Gt)?;
        }
        Ok(params)
    }

    // ── Types ─────────────────────────────────────────────────────────────────

    fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        let mut ty = self.parse_type_base()?;
        if matches!(self.current().kind, TokenKind::Question) {
            self.advance();
            ty = TypeExpr::Optional(Box::new(ty));
        }
        Ok(ty)
    }

    fn parse_type_base(&mut self) -> Result<TypeExpr, ParseError> {
        match &self.current().kind {
            TokenKind::TInt    => { self.advance(); Ok(TypeExpr::Named("int".into())) }
            TokenKind::TUint   => { self.advance(); Ok(TypeExpr::Named("uint".into())) }
            TokenKind::TI8     => { self.advance(); Ok(TypeExpr::Named("i8".into())) }
            TokenKind::TI16    => { self.advance(); Ok(TypeExpr::Named("i16".into())) }
            TokenKind::TI32    => { self.advance(); Ok(TypeExpr::Named("i32".into())) }
            TokenKind::TI64    => { self.advance(); Ok(TypeExpr::Named("i64".into())) }
            TokenKind::TI128   => { self.advance(); Ok(TypeExpr::Named("i128".into())) }
            TokenKind::TU8     => { self.advance(); Ok(TypeExpr::Named("u8".into())) }
            TokenKind::TU16    => { self.advance(); Ok(TypeExpr::Named("u16".into())) }
            TokenKind::TU32    => { self.advance(); Ok(TypeExpr::Named("u32".into())) }
            TokenKind::TU64    => { self.advance(); Ok(TypeExpr::Named("u64".into())) }
            TokenKind::TU128   => { self.advance(); Ok(TypeExpr::Named("u128".into())) }
            TokenKind::TF32    => { self.advance(); Ok(TypeExpr::Named("f32".into())) }
            TokenKind::TF64    => { self.advance(); Ok(TypeExpr::Named("f64".into())) }
            TokenKind::TBool   => { self.advance(); Ok(TypeExpr::Named("bool".into())) }
            TokenKind::TString => { self.advance(); Ok(TypeExpr::Named("string".into())) }
            TokenKind::TBytes  => { self.advance(); Ok(TypeExpr::Named("bytes".into())) }
            TokenKind::TVoid   => { self.advance(); Ok(TypeExpr::Void) }
            TokenKind::TAny    => { self.advance(); Ok(TypeExpr::Named("any".into())) }
            // Function type: fn(T1, T2, ...) -> R — used for higher-order
            // function parameters/returns, e.g. `f: fn(int) -> int`.
            // TypeExpr::Fn already existed in the AST but nothing produced
            // it, so `fn(...)` as a type previously fell through to the
            // catch-all error arm below — and worse, since `Fn` is also one
            // of `recover()`'s stopping tokens, the parser would get stuck
            // unable to make forward progress on recovery (it stops exactly
            // on the `fn` it can't parse, recover() sees it's already on a
            // stop-token and does nothing, and the outer item loop retries
            // the same token forever). This was the root cause of the
            // tests/core/functions_test.h# and types_test.h# hangs.
            TokenKind::Fn => {
                self.advance();
                self.expect(&TokenKind::LParen)?;
                let mut param_types = Vec::new();
                while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                    param_types.push(self.parse_type()?);
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); } else { break; }
                }
                self.expect(&TokenKind::RParen)?;
                let ret = if matches!(self.current().kind, TokenKind::Arrow) {
                    self.advance();
                    self.parse_type()?
                } else {
                    TypeExpr::Void
                };
                Ok(TypeExpr::Fn(param_types, Box::new(ret)))
            }
            TokenKind::BitAnd  => {
                self.advance();
                let mutable = if matches!(self.current().kind, TokenKind::Mut) { self.advance(); true } else { false };
                let inner = self.parse_type()?;
                Ok(if mutable { TypeExpr::RefMut(Box::new(inner)) } else { TypeExpr::Ref(Box::new(inner)) })
            }
            TokenKind::LBracket => {
                self.advance();
                let inner = self.parse_type()?;
                self.expect(&TokenKind::RBracket)?;
                Ok(TypeExpr::Array(Box::new(inner)))
            }
            TokenKind::LParen => {
                self.advance();
                let mut types = Vec::new();
                while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                    types.push(self.parse_type()?);
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                }
                self.expect(&TokenKind::RParen)?;
                Ok(TypeExpr::Tuple(types))
            }
            TokenKind::Ident(name) => {
                let name = name.clone(); self.advance();
                if matches!(self.current().kind, TokenKind::Lt) {
                    self.advance();
                    let mut args = Vec::new();
                    while !matches!(self.current().kind, TokenKind::Gt | TokenKind::EOF) {
                        args.push(self.parse_type()?);
                        if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                    }
                    self.expect(&TokenKind::Gt)?;
                    Ok(TypeExpr::Generic(name, args))
                } else {
                    Ok(TypeExpr::Named(name))
                }
            }
            _ => Err(self.error(
                format!("expected a type, found `{}`", self.current().text),
                    vec!["valid types: int, string, bool, f64, [T], T?, or a struct name".to_string()],
            )),
        }
    }

    // ── Statements ────────────────────────────────────────────────────────────

    pub fn parse_stmt(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.skip_newlines();
        match &self.current().kind {
            TokenKind::Let    => self.parse_let(),
            TokenKind::Return => {
                let span = self.current().span.clone(); self.advance();
                let expr = if !matches!(self.current().kind,
                                        TokenKind::Newline | TokenKind::EOF | TokenKind::End |
                                        TokenKind::Else    | TokenKind::Elsif)
                { Some(self.parse_expr(0)?) } else { None };
                Ok(vec![Stmt::Return(expr, span)])
            }
            TokenKind::Use => {
                let (kind, alias, span) = self.parse_import()?;
                Ok(vec![Stmt::Import(kind, alias, span)])
            }
            TokenKind::Break => {
                let span = self.current().span.clone(); self.advance();
                let val = if !matches!(self.current().kind,
                                       TokenKind::Newline | TokenKind::EOF | TokenKind::End)
                { Some(self.parse_expr(0)?) } else { None };
                Ok(vec![Stmt::Break(val, span)])
            }
            TokenKind::Continue => {
                let span = self.current().span.clone(); self.advance();
                Ok(vec![Stmt::Continue(span)])
            }
            TokenKind::Fn | TokenKind::Struct | TokenKind::Enum |
            TokenKind::Trait | TokenKind::Impl | TokenKind::Type | TokenKind::Pub => {
                let item = self.parse_item()?;
                Ok(vec![Stmt::Item(item)])
            }
            _ => {
                let expr = self.parse_expr(0)?;
                let span = expr.span().clone();
                Ok(vec![Stmt::Expr(expr, span)])
            }
        }
    }

    fn parse_let(&mut self) -> Result<Vec<Stmt>, ParseError> {
        let start = self.current().span.clone(); self.advance(); // let
        let mutable = if matches!(self.current().kind, TokenKind::Mut) { self.advance(); true } else { false };

        // Tuple destructuring: let (a, b) = expr  /  let mut (a, b) = expr
        // Desugars to a hidden temp binding plus one Stmt::Let per name,
        // each initialized via a tuple-field FieldAccess on the temp
        // (`.0`, `.1`, ...) — reuses existing, already-supported AST nodes
        // instead of introducing a new Stmt variant, which would require
        // updating several exhaustive `match stmt` sites in the compiler
        // crate (LLVM-dependent, not compile-verifiable in this sandbox).
        if matches!(self.current().kind, TokenKind::LParen) {
            self.advance();
            let mut names = Vec::new();
            while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                let (n, _) = self.expect_ident()?;
                names.push(n);
                if matches!(self.current().kind, TokenKind::Comma) { self.advance(); } else { break; }
            }
            self.expect(&TokenKind::RParen)?;
            self.expect(&TokenKind::Assign)?;
            let value = self.parse_expr(0)?;
            let span = start.merge(&self.current().span);

            let tmp_name = format!("__destructure_{}_{}", span.start.line, span.start.offset);
            let mut out = vec![Stmt::Let {
                name: tmp_name.clone(), ty: None, mutable: false,
                value: Some(value), span: span.clone(),
            }];
            for (idx, n) in names.into_iter().enumerate() {
                let field_access = Expr::FieldAccess(
                    Box::new(Expr::Ident(tmp_name.clone(), span.clone())),
                    idx.to_string(),
                    span.clone(),
                );
                out.push(Stmt::Let {
                    name: n, ty: None, mutable,
                    value: Some(field_access), span: span.clone(),
                });
            }
            return Ok(out);
        }

        let (name, _) = self.expect_ident()?;
        let ty = if matches!(self.current().kind, TokenKind::Colon) {
            self.advance(); Some(self.parse_type()?)
        } else { None };
        let value = if matches!(self.current().kind, TokenKind::Assign) {
            self.advance(); Some(self.parse_expr(0)?)
        } else { None };
        let span = start.merge(&self.current().span);
        Ok(vec![Stmt::Let { name, ty, mutable, value, span }])
    }

    // ── Expressions ────────────────────────────────────────────────────────────

    fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            // NOTE: do NOT skip_newlines() here. If the current token is
            // Newline, the expression ends at end-of-line (statement
            // boundary) — break immediately without consuming it, so the
            // outer statement loop can see it.
            //
            // Multi-line continuation (operator at END of line, e.g.
            // `"a" +\n"b"`) is handled differently: the operator token is
            // consumed BEFORE we reach a Newline, and parse_prefix() (called
            // for the rhs) skips the following newline itself.
            if matches!(self.current().kind,
                TokenKind::EOF | TokenKind::End | TokenKind::Newline |
                TokenKind::Comma | TokenKind::RParen | TokenKind::RBracket |
                TokenKind::RBrace | TokenKind::Semicolon)
            {
                // SPECIAL CASE: method-chain continuation.
                //   result.trim()
                //       .to_lower()
                //       .replace("a", "b")
                // Here `.to_lower()` starts the next line — the *leading*
                // token is `.`. This is the one case where a leading
                // operator on the next line is unambiguous: no valid H#
                // expression ends with a bare value immediately followed
                // by a statement that starts with `.` (field/method access
                // on a fresh value with no receiver isn't valid syntax).
                // So: if the current token is Newline, peek past all
                // consecutive newlines; if the first real token is `.`,
                // skip the newlines and continue the chain instead of
                // ending the expression here.
                if matches!(self.current().kind, TokenKind::Newline) {
                    let mut peek = self.pos;
                    while matches!(self.tokens.get(peek).map(|t| &t.kind), Some(TokenKind::Newline)) {
                        peek += 1;
                    }
                    if matches!(self.tokens.get(peek).map(|t| &t.kind), Some(TokenKind::Dot)) {
                        self.skip_newlines();
                        // fall through to infix handling below (current is now `.`)
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }

            let (l_bp, r_bp) = match infix_bp(&self.current().kind) {
                Some(bp) => bp,
                None     => break,
            };
            if l_bp < min_bp { break; }

            let op_tok = self.advance().clone();
            let span   = lhs.span().merge(&op_tok.span);

            // Assignment
            if matches!(op_tok.kind, TokenKind::Assign) {
                let rhs = self.parse_expr(r_bp)?;
                let s = lhs.span().merge(rhs.span());
                lhs = Expr::Assign(Box::new(lhs), Box::new(rhs), s);
                continue;
            }
            // Compound assignment
            if let Some(op) = compound_op(&op_tok.kind) {
                let rhs = self.parse_expr(r_bp)?;
                let s = lhs.span().merge(rhs.span());
                lhs = Expr::CompoundAssign(Box::new(lhs), op, Box::new(rhs), s);
                continue;
            }
            // Method call / field access
            if matches!(op_tok.kind, TokenKind::Dot) {
                // Tuple field access: t.0, t.1, ... — the lexer tokenizes
                // a bare integer here (not an identifier), so handle it
                // before falling through to the identifier-based path used
                // for struct field access and method calls.
                if let TokenKind::Integer(n) = self.current().kind {
                    let idx_span = self.current().span.clone();
                    self.advance();
                    let s = lhs.span().merge(&idx_span);
                    lhs = Expr::FieldAccess(Box::new(lhs), n.to_string(), s);
                    continue;
                }
                let (name, _) = self.expect_ident()?;
                if matches!(self.current().kind, TokenKind::LParen) {
                    self.advance();
                    let args = self.parse_call_args()?;
                    let s = lhs.span().merge(&self.current().span);
                    lhs = Expr::MethodCall(Box::new(lhs), name, args, s);
                } else {
                    let s = lhs.span().merge(&self.current().span);
                    lhs = Expr::FieldAccess(Box::new(lhs), name, s);
                }
                continue;
            }
            // Index access
            if matches!(op_tok.kind, TokenKind::LBracket) {
                let idx = self.parse_expr(0)?;
                self.expect(&TokenKind::RBracket)?;
                let s = lhs.span().merge(&self.current().span);
                lhs = Expr::IndexAccess(Box::new(lhs), Box::new(idx), s);
                continue;
            }
            // Range
            if matches!(op_tok.kind, TokenKind::DotDot | TokenKind::DotDotEq) {
                let inclusive = matches!(op_tok.kind, TokenKind::DotDotEq);
                let rhs = self.parse_expr(r_bp)?;
                let s = lhs.span().merge(rhs.span());
                lhs = Expr::Range(Box::new(lhs), Box::new(rhs), inclusive, s);
                continue;
            }
            // Cast
            if matches!(op_tok.kind, TokenKind::As) {
                let ty = self.parse_type()?;
                lhs = Expr::Cast(Box::new(lhs), ty, span);
                continue;
            }
            // ? operator
            if matches!(op_tok.kind, TokenKind::Question) {
                let s = lhs.span().merge(&op_tok.span);
                lhs = Expr::Try(Box::new(lhs), s);
                continue;
            }
            // Binary operators
            if let Some(bin_op) = token_to_binop(&op_tok.kind) {
                let rhs = self.parse_expr(r_bp)?;
                let s = lhs.span().merge(rhs.span());
                lhs = Expr::BinOp(Box::new(lhs), bin_op, Box::new(rhs), s);
            }
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self) -> Result<Expr, ParseError> {
        // Skip leading newlines — handles multi-line expressions where a
        // binary operator (e.g. `+`) ends a line and the operand continues
        // on the next line. This is essential for long string concatenations:
        //   let s: string = "part1 " +
        //       "part2 " +
        //       "part3"
        self.skip_newlines();

        let start = self.current().span.clone();

        // await
        if matches!(self.current().kind, TokenKind::Await) {
            let span = self.current().span.clone(); self.advance();
            let inner = self.parse_expr(0)?;
            let s = span.merge(inner.span());
            return Ok(Expr::Await(Box::new(inner), s));
        }
        // Closure: |params| body
        if matches!(self.current().kind, TokenKind::Pipe) {
            return self.parse_closure_expr();
        }
        // Empty-parameter closure: || body. The lexer greedily tokenizes
        // `||` as a single TokenKind::Or (logical-or operator), since that
        // reading is far more common lexically — so a zero-parameter
        // closure can never be seen as two separate Pipe tokens the way
        // `parse_closure_expr` expects. Handle it here as a distinct case:
        // consume the Or token (it stands in for `||`) and parse the
        // closure body directly, with no parameters to collect.
        if matches!(self.current().kind, TokenKind::Or) {
            return self.parse_empty_param_closure_expr();
        }

        match self.current().kind.clone() {
            TokenKind::Integer(v) => {
                let span = self.current().span.clone(); self.advance();
                Ok(Expr::Literal(Literal::Int(v), span))
            }
            TokenKind::Float(v) => {
                let span = self.current().span.clone(); self.advance();
                Ok(Expr::Literal(Literal::Float(v), span))
            }
            TokenKind::StringLit(s) => {
                let span = self.current().span.clone(); self.advance();
                Ok(Expr::Literal(Literal::String(s), span))
            }
            TokenKind::InterpStringLit(s) => {
                let span = self.current().span.clone(); self.advance();
                Ok(self.parse_interpolated_string(s, span))
            }
            TokenKind::Bool(b) => {
                let span = self.current().span.clone(); self.advance();
                Ok(Expr::Literal(Literal::Bool(b), span))
            }
            TokenKind::Nil => {
                let span = self.current().span.clone(); self.advance();
                Ok(Expr::Literal(Literal::Nil, span))
            }
            TokenKind::Self_ => {
                let span = self.current().span.clone(); self.advance();
                Ok(Expr::SelfExpr(span))
            }
            TokenKind::Write | TokenKind::Manual | TokenKind::Arena => {
                let name = match self.current().kind {
                    TokenKind::Write  => "write",
                    TokenKind::Manual => "manual",
                    TokenKind::Arena  => "arena",
                    _                 => unreachable!(),
                }.to_string();
                let span = self.current().span.clone(); self.advance();
                if matches!(self.current().kind, TokenKind::LParen) {
                    self.advance();
                    let args = self.parse_call_args()?;
                    let s = span.merge(&self.current().span);
                    Ok(Expr::Call(Box::new(Expr::Ident(name, span.clone())), args, s))
                } else {
                    Ok(Expr::Ident(name, span))
                }
            }
            TokenKind::Ident(_)   => self.parse_ident_expr(),
            // A soft keyword immediately followed by `::` is being used as
            // the first segment of a module path (e.g. `async::spawn(...)`,
            // since `async` is also commonly the alias users `use "std ->
            // async_" from "async"`). This never shadows the keyword's real
            // meaning elsewhere in the grammar — `async fn ...`, `mod Foo
            // is ... end`, etc. are all handled earlier, at the statement/
            // item level, before expression parsing is ever reached for
            // those tokens; only a bare `KEYWORD::` sequence in expression
            // position reaches here. Note: `Match`, `For`, and `Self_` are
            // deliberately NOT included here even though they're also soft
            // keywords — each has its own earlier, unconditional arm in
            // this same match (`TokenKind::Match => self.parse_match()`,
            // etc.) that would always intercept first, making a guarded
            // entry for them here permanently unreachable.
            TokenKind::New | TokenKind::Write | TokenKind::Type | TokenKind::End |
            TokenKind::As | TokenKind::Is | TokenKind::From | TokenKind::Use |
            TokenKind::Mod | TokenKind::Async | TokenKind::Await | TokenKind::In
                if matches!(self.tokens.get(self.pos + 1).map(|t| &t.kind), Some(TokenKind::ColonColon)) =>
            {
                let (name, name_span) = self.expect_path_segment()?;
                self.parse_ident_expr_from(name, name_span)
            }
            TokenKind::Minus      => {
                self.advance();
                // Bind tighter than any binary operator but let postfix
                // `.method()` / `[index]` / `(call)` on the operand still
                // apply first — see the long comment on the TokenKind::Not
                // arm just below for why parse_prefix() alone is wrong here.
                let e = self.parse_expr(29)?;
                let s = start.merge(e.span());
                Ok(Expr::UnOp(UnOp::Neg, Box::new(e), s))
            }
            TokenKind::Not => {
                self.advance();
                // CRITICAL: must NOT be parse_prefix() here. parse_prefix()
                // parses only a single primary/prefix expression with no
                // postfix (`.method()`, `[index]`, `(call)`) handling at
                // all — that logic lives in parse_expr's Pratt loop, which
                // parse_prefix() never reaches. The old `parse_prefix()`
                // call meant `!map.contains_key(x)` parsed as
                // `(!map).contains_key(x)` (negate first, THEN try to call
                // a method on the resulting bool — a runtime type error)
                // instead of the obviously-intended `!(map.contains_key(x))`.
                // Calling parse_expr(29) — just below Dot/LBracket's binding
                // power of 30 — lets the operand's full postfix chain
                // resolve first, while still stopping before lower-
                // precedence binary operators so `!a == b` keeps meaning
                // `(!a) == b`.
                let e = self.parse_expr(29)?;
                let s = start.merge(e.span());
                Ok(Expr::UnOp(UnOp::Not, Box::new(e), s))
            }
            TokenKind::BitNot => {
                self.advance();
                let e = self.parse_expr(29)?;
                let s = start.merge(e.span());
                Ok(Expr::UnOp(UnOp::BitNot, Box::new(e), s))
            }
            TokenKind::BitAnd => {
                self.advance();
                let mutable = if matches!(self.current().kind, TokenKind::Mut) { self.advance(); true } else { false };
                let e = self.parse_prefix()?;
                let s = start.merge(e.span());
                Ok(Expr::UnOp(if mutable { UnOp::RefMut } else { UnOp::Ref }, Box::new(e), s))
            }
            TokenKind::Star => {
                self.advance();
                let e = self.parse_prefix()?;
                let s = start.merge(e.span());
                Ok(Expr::UnOp(UnOp::Deref, Box::new(e), s))
            }
            TokenKind::LParen => {
                self.advance();
                if matches!(self.current().kind, TokenKind::RParen) {
                    self.advance();
                    return Ok(Expr::TupleLit(vec![], start));
                }
                let expr = self.parse_expr(0)?;
                if matches!(self.current().kind, TokenKind::Comma) {
                    let mut elems = vec![expr];
                    while matches!(self.current().kind, TokenKind::Comma) {
                        self.advance();
                        if matches!(self.current().kind, TokenKind::RParen) { break; }
                        elems.push(self.parse_expr(0)?);
                    }
                    self.expect(&TokenKind::RParen)?;
                    let s = start.merge(&self.current().span);
                    Ok(Expr::TupleLit(elems, s))
                } else {
                    self.expect(&TokenKind::RParen)?;
                    Ok(expr)
                }
            }
            TokenKind::LBracket => {
                self.advance();
                let mut elems = Vec::new();
                while !matches!(self.current().kind, TokenKind::RBracket | TokenKind::EOF) {
                    self.skip_newlines();
                    if matches!(self.current().kind, TokenKind::RBracket) { break; }
                    elems.push(self.parse_expr(0)?);
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                }
                self.expect(&TokenKind::RBracket)?;
                let s = start.merge(&self.current().span);
                Ok(Expr::ArrayLit(elems, s))
            }
            TokenKind::If      => self.parse_if(),
            TokenKind::Match   => self.parse_match(),
            TokenKind::While   => self.parse_while(),
            TokenKind::For     => self.parse_for(),
            TokenKind::Is      => {
                let body = self.parse_block()?;
                let s = start.merge(&self.current().span);
                Ok(Expr::Do { body, span: s })
            }
            TokenKind::Unsafe  => self.parse_unsafe_block(start),
            TokenKind::Return  => {
                self.advance();
                let val = if !matches!(self.current().kind,
                                       TokenKind::Newline | TokenKind::EOF | TokenKind::End |
                                       TokenKind::Comma   | TokenKind::RParen)
                { Some(Box::new(self.parse_expr(0)?)) } else { None };
                let s = start.merge(&self.current().span);
                Ok(Expr::Return(val, s))
            }
            _ => Err(ParseError::new(
                ParseErrorKind::UnexpectedToken,
                self.current().span.clone(),
                                     format!("unexpected token `{}`", self.current().text),
                                         vec!["expected an expression".to_string()],
            )),
        }
    }

    fn parse_ident_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        let (name, _) = self.expect_ident()?;
        self.parse_ident_expr_from(name, start)
    }

    /// The body of `parse_ident_expr`, parameterized over an
    /// already-consumed first segment/name and its span. Used both by
    /// `parse_ident_expr` (the normal `Ident`-led case) and by the
    /// soft-keyword-led path case in `parse_primary` (e.g. `async::spawn`,
    /// where `async` was consumed via `expect_path_segment` instead of
    /// `expect_ident` since it's a reserved keyword token).
    fn parse_ident_expr_from(&mut self, name: String, start: Span) -> Result<Expr, ParseError> {
        // Module path: name::seg::seg ... (e.g. json::parse, math::sqrt, mod::sub::fn)
        if matches!(self.current().kind, TokenKind::ColonColon) {
            let mut segments = vec![name];
            while matches!(self.current().kind, TokenKind::ColonColon) {
                self.advance(); // consume ::
                let (seg, _) = self.expect_path_segment()?;
                segments.push(seg);
            }
            let path_span = start.merge(&self.current().span);

            // Path used as a call: module::function(args)
            if matches!(self.current().kind, TokenKind::LParen) {
                self.advance();
                let args = self.parse_call_args()?;
                let s = start.merge(&self.current().span);
                let callee = Expr::Path(segments, path_span);
                return Ok(Expr::Call(Box::new(callee), args, s));
            }

            // Path used as a struct literal: module::Type { field: val }
            if matches!(self.current().kind, TokenKind::LBrace) {
                self.advance();
                let mut fields = Vec::new();
                self.skip_newlines();
                while !matches!(self.current().kind, TokenKind::RBrace | TokenKind::EOF) {
                    self.skip_newlines();
                    if matches!(self.current().kind, TokenKind::RBrace) { break; }
                    let (fname, _) = self.expect_ident()?;
                    self.expect(&TokenKind::Colon)?;
                    let fval = self.parse_expr(0)?;
                    fields.push((fname, fval));
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                    self.skip_newlines();
                }
                self.expect(&TokenKind::RBrace)?;
                let s = start.merge(&self.current().span);
                let full_name = segments.join("::");
                return Ok(Expr::StructLit(full_name, fields, s));
            }

            // Bare path: module::CONST or module::Variant
            return Ok(Expr::Path(segments, path_span));
        }

        // Struct literal: Name { field: val, ... }
        if matches!(self.current().kind, TokenKind::LBrace) {
            self.advance();
            let mut fields = Vec::new();
            self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::RBrace | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::RBrace) { break; }
                let (fname, _) = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                let fval = self.parse_expr(0)?;
                fields.push((fname, fval));
                if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                self.skip_newlines();
            }
            self.expect(&TokenKind::RBrace)?;
            let s = start.merge(&self.current().span);
            return Ok(Expr::StructLit(name, fields, s));
        }
        // Function call: name(args)
        if matches!(self.current().kind, TokenKind::LParen) {
            self.advance();
            let args = self.parse_call_args()?;
            let s = start.merge(&self.current().span);
            return Ok(Expr::Call(Box::new(Expr::Ident(name, start)), args, s));
        }
        Ok(Expr::Ident(name, start))
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut args = Vec::new();
        while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::RParen) { break; }
            args.push(self.parse_expr(0)?);
            if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(args)
    }

    // ── if / else if / else — v0.7 FIXED ─────────────────────────────────────

    fn parse_if(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // consume `if`

        let condition = self.parse_expr(0)?;
        self.skip_newlines();

        // Must have `is`
        if !matches!(self.current().kind, TokenKind::Is) {
            return Err(self.error(
                "expected `is` after if condition",
                vec!["write: if condition is ... end".to_string()],
            ));
        }
        self.advance(); // consume `is`
        self.skip_newlines();

        // Parse then body — stop at else/elsif/end
        let mut then_body = Vec::new();
        loop {
            self.skip_newlines();
            if matches!(self.current().kind,
                TokenKind::End | TokenKind::EOF |
                TokenKind::Else | TokenKind::Elsif)
            { break; }
            match self.parse_stmt() {
                Ok(s)  => then_body.extend(s),
                Err(e) => { self.errors.report(e); self.recover(); }
            }
        }

        let mut elsif_branches: Vec<(Expr, Vec<Stmt>)> = Vec::new();
        let mut else_body: Option<Vec<Stmt>>            = None;

        // Parse elsif / else chains — v0.7 fix: handle both `elsif` and `else if`
        loop {
            self.skip_newlines();

            if matches!(self.current().kind, TokenKind::Elsif) {
                // elsif cond is ... (no end — falls through to next elsif/else/end)
                self.advance(); // consume `elsif`
                let cond = self.parse_expr(0)?;
                self.skip_newlines();
                if !matches!(self.current().kind, TokenKind::Is) {
                    return Err(self.error("expected `is` after elsif condition", vec![]));
                }
                self.advance(); // consume `is`
                self.skip_newlines();

                let mut branch_body = Vec::new();
                loop {
                    self.skip_newlines();
                    if matches!(self.current().kind,
                        TokenKind::End | TokenKind::EOF |
                        TokenKind::Else | TokenKind::Elsif)
                    { break; }
                    match self.parse_stmt() {
                        Ok(s)  => branch_body.extend(s),
                        Err(e) => { self.errors.report(e); self.recover(); }
                    }
                }
                elsif_branches.push((cond, branch_body));
                continue;
            }

            if matches!(self.current().kind, TokenKind::Else) {
                self.advance(); // consume `else`
                self.skip_newlines();

                // `else if cond is` — treat as elsif (two-token form)
                if matches!(self.current().kind, TokenKind::If) {
                    self.advance(); // consume `if`
                    let cond = self.parse_expr(0)?;
                    self.skip_newlines();
                    if !matches!(self.current().kind, TokenKind::Is) {
                        return Err(self.error("expected `is` after else if condition", vec![]));
                    }
                    self.advance(); // consume `is`
                    self.skip_newlines();

                    let mut branch_body = Vec::new();
                    loop {
                        self.skip_newlines();
                        if matches!(self.current().kind,
                            TokenKind::End | TokenKind::EOF |
                            TokenKind::Else | TokenKind::Elsif)
                        { break; }
                        match self.parse_stmt() {
                            Ok(s)  => branch_body.extend(s),
                            Err(e) => { self.errors.report(e); self.recover(); }
                        }
                    }
                    elsif_branches.push((cond, branch_body));
                    continue;
                }

                // Plain `else is` or `else` (v0.7: both forms)
                // Skip optional `is` after `else`
                if matches!(self.current().kind, TokenKind::Is) {
                    self.advance();
                }
                self.skip_newlines();

                let mut body = Vec::new();
                loop {
                    self.skip_newlines();
                    if matches!(self.current().kind, TokenKind::End | TokenKind::EOF) { break; }
                    match self.parse_stmt() {
                        Ok(s)  => body.extend(s),
                        Err(e) => { self.errors.report(e); self.recover(); }
                    }
                }
                else_body = Some(body);
                break;
            }

            break;
        }

        // Consume the final `end`
        if matches!(self.current().kind, TokenKind::End) {
            self.advance();
        }

        let s = start.merge(&self.current().span);
        Ok(Expr::If {
            condition: Box::new(condition),
           then_body,
           elsif_branches,
           else_body,
               span: s,
        })
    }

    // ── match ─────────────────────────────────────────────────────────────────

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // consume `match`
        let subject = self.parse_expr(0)?;
        self.skip_newlines();
        self.expect(&TokenKind::Is)?;
        self.skip_newlines();

        let mut arms = Vec::new();
        while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::End) { break; }

            let arm_span = self.current().span.clone();

            // Parse pattern (may be `pat | pat | ...`)
            let pattern = self.parse_pattern_or()?;

            // Optional guard: if cond
            let guard = if matches!(self.current().kind, TokenKind::If) {
                self.advance();
                Some(self.parse_expr(0)?)
            } else { None };

            // => body
            self.expect(&TokenKind::FatArrow)?;
            self.skip_newlines();

            let body = if matches!(self.current().kind, TokenKind::Is) {
                // Multi-statement arm: => is ... end
                self.parse_block()?
            } else {
                // Single expression arm
                let e = self.parse_expr(0)?;
                let s = e.span().clone();
                vec![Stmt::Expr(e, s)]
            };

            arms.push(MatchArm { pattern, guard, body, span: arm_span });
            if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
            self.skip_newlines();
        }
        self.expect(&TokenKind::End)?;
        let s = start.merge(&self.current().span);
        Ok(Expr::Match { subject: Box::new(subject), arms, span: s })
    }

    // ── Patterns ──────────────────────────────────────────────────────────────

    /// Parse a pattern that may be `pat | pat | ...`
    fn parse_pattern_or(&mut self) -> Result<Pattern, ParseError> {
        let span  = self.current().span.clone();
        let first = self.parse_pattern()?;
        if !matches!(self.current().kind, TokenKind::Pipe) {
            return Ok(first);
        }
        let mut pats = vec![first];
        while matches!(self.current().kind, TokenKind::Pipe) {
            self.advance();
            // Allow the next alternative to start on the following line:
            //   "a" |
            //   "b" |
            //   "c" => ...
            // The `|` is consumed while still on the current line; skip the
            // newline before parsing the next pattern alternative.
            self.skip_newlines();
            pats.push(self.parse_pattern()?);
        }
        Ok(Pattern::Or(pats, span))
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        let start = self.current().span.clone();
        match self.current().kind.clone() {
            TokenKind::Ident(ref name) if name == "_" => {
                self.advance(); Ok(Pattern::Wildcard(start))
            }
            TokenKind::Ident(name) => {
                self.advance();
                // Qualified enum variant pattern: Type::Variant or
                // Type::Variant(p1, p2, ...). Mirrors the Expr-side
                // Type::Variant(...) construction syntax — patterns need
                // the same qualified form to match values built that way
                // (see Color::Custom(_, _, _) in match arms).
                if matches!(self.current().kind, TokenKind::ColonColon) {
                    self.advance();
                    let (variant, _) = self.expect_path_segment()?;
                    let inner = if matches!(self.current().kind, TokenKind::LParen) {
                        self.advance();
                        let mut pats = Vec::new();
                        while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                            pats.push(self.parse_pattern()?);
                            if matches!(self.current().kind, TokenKind::Comma) { self.advance(); } else { break; }
                        }
                        self.expect(&TokenKind::RParen)?;
                        pats
                    } else {
                        Vec::new()
                    };
                    let s = start.merge(&self.current().span);
                    return Ok(Pattern::Enum { qualified_type: Some(name), variant, inner, span: s });
                }
                // Unqualified enum variant with fields: Variant(p1, p2, ...)
                if matches!(self.current().kind, TokenKind::LParen) {
                    self.advance();
                    let mut pats = Vec::new();
                    while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                        pats.push(self.parse_pattern()?);
                        if matches!(self.current().kind, TokenKind::Comma) { self.advance(); } else { break; }
                    }
                    self.expect(&TokenKind::RParen)?;
                    let s = start.merge(&self.current().span);
                    Ok(Pattern::Enum { qualified_type: None, variant: name, inner: pats, span: s })
                } else {
                    Ok(Pattern::Ident(name, start))
                }
            }
            TokenKind::Integer(v)  => { self.advance(); Ok(Pattern::Literal(Literal::Int(v), start)) }
            TokenKind::StringLit(s) => { self.advance(); Ok(Pattern::Literal(Literal::String(s), start)) }
            // A string pattern containing `{...}` has no special meaning in
            // match-pattern position (patterns match literal values, they
            // don't interpolate) — treat its raw source text as the literal
            // string to match against.
            TokenKind::InterpStringLit(s) => { self.advance(); Ok(Pattern::Literal(Literal::String(s), start)) }
            TokenKind::Bool(b)     => { self.advance(); Ok(Pattern::Literal(Literal::Bool(b), start)) }
            TokenKind::Nil         => { self.advance(); Ok(Pattern::Literal(Literal::Nil, start)) }
            TokenKind::Minus       => {
                // Negative integer pattern
                self.advance();
                if let TokenKind::Integer(v) = self.current().kind.clone() {
                    self.advance();
                    Ok(Pattern::Literal(Literal::Int(-v), start))
                } else {
                    Err(self.error("expected integer after `-` in pattern", vec![]))
                }
            }
            TokenKind::LParen => {
                // Tuple pattern: (a, b, ...)
                self.advance();
                let mut pats = Vec::new();
                while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                    pats.push(self.parse_pattern()?);
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                }
                self.expect(&TokenKind::RParen)?;
                let s = start.merge(&self.current().span);
                Ok(Pattern::Tuple(pats, s))
            }
            TokenKind::DotDot => {
                // Range pattern: start..end or start..=end
                // handled higher up via parse_pattern_or — standalone .. means rest-of-tuple
                self.advance();
                Ok(Pattern::Wildcard(start))
            }
            _ => Err(self.error(
                format!("expected pattern, found `{}`", self.current().text),
                    vec!["valid patterns: name, literal, Variant(inner), (a, b), or _".to_string()],
            )),
        }
    }

    // ── while / for ───────────────────────────────────────────────────────────

    fn parse_while(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone(); self.advance();
        let condition = self.parse_expr(0)?;
        self.skip_newlines();
        let body = self.parse_block()?;
        let s = start.merge(&self.current().span);
        Ok(Expr::While { condition: Box::new(condition), body, span: s })
    }

    fn parse_for(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone(); self.advance();
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expr(0)?;
        self.skip_newlines();
        let body = self.parse_block()?;
        let s = start.merge(&self.current().span);
        Ok(Expr::For { pattern, iterable: Box::new(iterable), body, span: s })
    }

    // ── unsafe block ──────────────────────────────────────────────────────────

    fn parse_unsafe_block(&mut self, start: Span) -> Result<Expr, ParseError> {
        self.advance(); // consume `unsafe`
        let arena: Option<ArenaConfig> = if matches!(self.current().kind, TokenKind::Arena) {
            self.advance();
            let kind = if matches!(self.current().kind, TokenKind::LParen) {
                self.advance();
                let k = match &self.current().kind.clone() {
                    TokenKind::Ident(s) if s == "fixed"   => { self.advance(); ArenaKind::Fixed }
                    TokenKind::Ident(s) if s == "pool"    => { self.advance(); ArenaKind::Pool }
                    TokenKind::Ident(s) if s == "page"    => { self.advance(); ArenaKind::Page }
                    TokenKind::Ident(s) if s == "ring"    => { self.advance(); ArenaKind::Ring }
                    TokenKind::Integer(_)                  => ArenaKind::General,
                    _                                      => ArenaKind::General,
                };
                let size = if let TokenKind::Integer(n) = self.current().kind.clone() {
                    self.advance(); Some(n as usize)
                } else { None };
                self.expect(&TokenKind::RParen)?;
                (k, size)
            } else { (ArenaKind::General, None) };
            Some(ArenaConfig { mode: UnsafeMode::Arena { kind: kind.0, size: kind.1 } })
        } else if matches!(self.current().kind, TokenKind::Manual) {
            self.advance();
            let manual_kind = if matches!(self.current().kind, TokenKind::LParen) {
                self.advance();
                let k = match &self.current().kind.clone() {
                    TokenKind::Ident(s) if s == "classic" => { self.advance(); ManualKind::Classic }
                    _ => ManualKind::Modern,
                };
                self.expect(&TokenKind::RParen)?;
                k
            } else { ManualKind::Modern };
            Some(ArenaConfig { mode: UnsafeMode::Manual(manual_kind) })
        } else {
            Some(ArenaConfig { mode: UnsafeMode::Raw })
        };
        let body = self.parse_block()?;
        let s = start.merge(&self.current().span);
        Ok(Expr::Unsafe(body, arena, s))
    }

    // ── Closure ───────────────────────────────────────────────────────────────

    /// Parse a zero-parameter closure body after the lexer has already
    /// consumed `||` as a single `TokenKind::Or` token. See the call site
    /// in `parse_primary` for why this needs to be a separate path from
    /// `parse_closure_expr` (which expects two distinct `Pipe` tokens).
    fn parse_empty_param_closure_expr(&mut self) -> Result<Expr, ParseError> {
        let span = self.current().span.clone();
        self.advance(); // consume the `||` (lexed as one Or token)
        let return_type = if matches!(self.current().kind, TokenKind::Arrow) {
            self.advance(); Some(self.parse_type()?)
        } else { None };
        let body = if matches!(self.current().kind, TokenKind::Is) {
            self.parse_block()?
        } else {
            let e = self.parse_expr(0)?;
            let s = e.span().clone();
            vec![Stmt::Return(Some(e), s)]
        };
        let end_sp = self.current().span.clone();
        Ok(Expr::Closure { params: Vec::new(), return_type, body, span: span.merge(&end_sp) })
    }

    fn parse_closure_expr(&mut self) -> Result<Expr, ParseError> {
        let span = self.current().span.clone();
        self.advance(); // consume opening |
        let mut params = Vec::new();
        while !matches!(self.current().kind, TokenKind::Pipe | TokenKind::EOF) {
            let p_span  = self.current().span.clone();
            let mutable = if matches!(self.current().kind, TokenKind::Mut) { self.advance(); true } else { false };
            let (name, _) = self.expect_ident()?;
            let ty = if matches!(self.current().kind, TokenKind::Colon) {
                self.advance(); self.parse_type()?
            } else { TypeExpr::Named("int".into()) };
            params.push(Param { name, ty, mutable, span: p_span });
            if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
        }
        if matches!(self.current().kind, TokenKind::Pipe) { self.advance(); }
        let return_type = if matches!(self.current().kind, TokenKind::Arrow) {
            self.advance(); Some(self.parse_type()?)
        } else { None };
        let body = if matches!(self.current().kind, TokenKind::Is) {
            self.parse_block()?
        } else {
            let e = self.parse_expr(0)?;
            let s = e.span().clone();
            vec![Stmt::Return(Some(e), s)]
        };
        let end_sp = self.current().span.clone();
        Ok(Expr::Closure { params, return_type, body, span: span.merge(&end_sp) })
    }

    // ── String interpolation ──────────────────────────────────────────────────

    fn parse_interpolated_string(&mut self, raw: String, span: Span) -> Expr {
        let mut parts: Vec<InterpPart> = Vec::new();
        let bytes = raw.as_bytes();
        let mut i = 0;
        let mut text_start = 0;

        while i < bytes.len() {
            // `{{` — escaped literal brace. Flush text up to (and
            // including, as a literal `{`) this marker, then continue
            // scanning from past `}}` is NOT assumed here — only the `{{`
            // pair is collapsed to one `{`; a lone `}}` later in plain text
            // is likewise collapsed to one `}` when encountered below. This
            // mirrors how `{{` / `}}` are used independently as escapes,
            // not as a single combined `{{...}}` construct.
            if i + 1 < bytes.len() && bytes[i] == b'{' && bytes[i + 1] == b'{' {
                let text = &raw[text_start..i];
                parts.push(InterpPart::Text(format!("{}{{", text)));
                i += 2;
                text_start = i;
                continue;
            }
            if i + 1 < bytes.len() && bytes[i] == b'}' && bytes[i + 1] == b'}' {
                let text = &raw[text_start..i];
                parts.push(InterpPart::Text(format!("{}}}", text)));
                i += 2;
                text_start = i;
                continue;
            }
            if bytes[i] == b'{' {
                // Flush any accumulated literal text before the marker.
                let text = &raw[text_start..i];
                if !text.is_empty() { parts.push(InterpPart::Text(text.to_string())); }
                i += 1;
                let expr_start = i;
                let mut depth = 1usize;
                // Track whether we're inside a nested string literal (e.g.
                // {if x == "}" is "yes" else "no" end}). Braces inside a
                // string must not affect `depth` — otherwise a `}` inside
                // a quoted string is mistaken for the end of `{...}`,
                // silently truncating the interpolated expression.
                let mut in_str  = false;
                let mut escaped = false;
                while i < bytes.len() {
                    let c = bytes[i];
                    if in_str {
                        if escaped {
                            escaped = false;
                        } else if c == b'\\' {
                            escaped = true;
                        } else if c == b'"' {
                            in_str = false;
                        }
                        i += 1;
                        continue;
                    }
                    match c {
                        b'"' => { in_str = true; i += 1; }
                        b'{' => { depth += 1; i += 1; }
                        b'}' => { depth -= 1; if depth == 0 { break; } i += 1; }
                        _    => { i += 1; }
                    }
                }
                let expr_src = raw[expr_start..i].trim();
                i += 1; // consume the closing '}'
                text_start = i;
                let expr = if expr_src.is_empty() {
                    Expr::Literal(Literal::String(String::new()), span.clone())
                } else {
                    let sub = format!("fn __interp__() is\n    return {}\nend", expr_src);
                    let result = crate::parse(&sub, "<interp>");
                    if !result.has_errors() {
                        result.module.items.into_iter().find_map(|item| {
                            if let Item::FnDef(f) = item {
                                f.body.into_iter().find_map(|s| {
                                    if let Stmt::Return(Some(e), _) = s { Some(e) } else { None }
                                })
                            } else { None }
                        }).unwrap_or_else(|| Expr::Ident(expr_src.to_string(), span.clone()))
                    } else if expr_src.chars().all(|c| c.is_alphanumeric() || c == '_') {
                        Expr::Ident(expr_src.to_string(), span.clone())
                    } else {
                        Expr::Literal(Literal::String(format!("{{{}}}", expr_src)), span.clone())
                    }
                };
                parts.push(InterpPart::Expr(Box::new(expr)));
            } else {
                // Advance by one full UTF-8 character (not one byte) to
                // stay on a char boundary for the next `raw[text_start..i]`
                // slice — `i` must always land on a valid UTF-8 boundary.
                let ch_len = utf8_char_len_at(bytes, i);
                i += ch_len;
            }
        }
        let tail = &raw[text_start..];
        if !tail.is_empty() { parts.push(InterpPart::Text(tail.to_string())); }

        if parts.len() == 1 {
            if let InterpPart::Text(t) = &parts[0] {
                return Expr::Literal(Literal::String(t.clone()), span);
            }
        }
        if parts.is_empty() { return Expr::Literal(Literal::String(String::new()), span); }
        Expr::Literal(Literal::Interpolated(parts), span)
    }
}

// ── Pratt helpers ─────────────────────────────────────────────────────────────

/// Returns the byte length of the UTF-8 character starting at byte index
/// `i` in `bytes`, based on the leading byte's high-bit pattern. Used by
/// `parse_interpolated_string` to advance one full character at a time
/// through plain-text spans (which may contain multi-byte characters like
/// Polish ą/ę/ć/ł/ń/ó/ś/ż/ź) without ever landing mid-character, which
/// would otherwise corrupt the subsequent `raw[text_start..i]` string
/// slice (a non-char-boundary slice index panics in Rust).
fn utf8_char_len_at(bytes: &[u8], i: usize) -> usize {
    match bytes.get(i) {
        None => 1,
        Some(b) if b & 0x80 == 0x00 => 1, // 0xxxxxxx — ASCII
        Some(b) if b & 0xE0 == 0xC0 => 2, // 110xxxxx — 2-byte sequence
        Some(b) if b & 0xF0 == 0xE0 => 3, // 1110xxxx — 3-byte sequence
        Some(b) if b & 0xF8 == 0xF0 => 4, // 11110xxx — 4-byte sequence
        Some(_) => 1, // continuation byte encountered unexpectedly — advance
                      // by 1 to avoid an infinite loop; shouldn't happen for
                      // well-formed UTF-8 input.
    }
}

fn infix_bp(kind: &TokenKind) -> Option<(u8, u8)> {
    match kind {
        TokenKind::Question                                          => Some((100, 101)),
        TokenKind::Assign | TokenKind::PlusAssign |
        TokenKind::MinusAssign | TokenKind::StarAssign |
        TokenKind::SlashAssign                                       => Some((2, 1)),
        TokenKind::Or                                                => Some((4, 5)),
        TokenKind::And                                               => Some((6, 7)),
        TokenKind::Pipe                                              => Some((8, 9)),
        TokenKind::BitXor                                            => Some((9, 10)),
        TokenKind::BitAnd                                            => Some((10, 11)),
        TokenKind::Eq | TokenKind::NotEq                            => Some((14, 15)),
        TokenKind::Lt | TokenKind::Gt | TokenKind::LtEq | TokenKind::GtEq => Some((16, 17)),
        TokenKind::Shl | TokenKind::Shr                             => Some((18, 19)),
        TokenKind::Plus | TokenKind::Minus                          => Some((20, 21)),
        TokenKind::Star | TokenKind::Slash | TokenKind::Percent     => Some((22, 23)),
        TokenKind::As                                                => Some((24, 25)),
        TokenKind::Dot                                               => Some((30, 31)),
        TokenKind::LBracket                                          => Some((30, 31)),
        TokenKind::DotDot | TokenKind::DotDotEq                    => Some((18, 19)),
        _ => None,
    }
}

fn token_to_binop(kind: &TokenKind) -> Option<BinOp> {
    match kind {
        TokenKind::Plus    => Some(BinOp::Add),
        TokenKind::Minus   => Some(BinOp::Sub),
        TokenKind::Star    => Some(BinOp::Mul),
        TokenKind::Slash   => Some(BinOp::Div),
        TokenKind::Percent => Some(BinOp::Mod),
        TokenKind::Eq      => Some(BinOp::Eq),
        TokenKind::NotEq   => Some(BinOp::NotEq),
        TokenKind::Lt      => Some(BinOp::Lt),
        TokenKind::Gt      => Some(BinOp::Gt),
        TokenKind::LtEq    => Some(BinOp::LtEq),
        TokenKind::GtEq    => Some(BinOp::GtEq),
        TokenKind::And     => Some(BinOp::And),
        TokenKind::Or      => Some(BinOp::Or),
        TokenKind::BitAnd  => Some(BinOp::BitAnd),
        TokenKind::BitXor  => Some(BinOp::BitXor),
        TokenKind::Pipe    => Some(BinOp::BitOr),
        TokenKind::Shl     => Some(BinOp::Shl),
        TokenKind::Shr     => Some(BinOp::Shr),
        _ => None,
    }
}

fn compound_op(kind: &TokenKind) -> Option<BinOp> {
    match kind {
        TokenKind::PlusAssign  => Some(BinOp::Add),
        TokenKind::MinusAssign => Some(BinOp::Sub),
        TokenKind::StarAssign  => Some(BinOp::Mul),
        TokenKind::SlashAssign => Some(BinOp::Div),
        _ => None,
    }
}

fn token_kind_name(kind: &TokenKind) -> &'static str {
    match kind {
        TokenKind::LParen    => "(",
        TokenKind::RParen    => ")",
        TokenKind::LBrace    => "{",
        TokenKind::RBrace    => "}",
        TokenKind::LBracket  => "[",
        TokenKind::RBracket  => "]",
        TokenKind::Colon     => ":",
        TokenKind::ColonColon => "::",
        TokenKind::Comma     => ",",
        TokenKind::Arrow     => "->",
        TokenKind::FatArrow  => "=>",
        TokenKind::Assign    => "=",
        TokenKind::Is        => "is",
        TokenKind::End       => "end",
        TokenKind::In        => "in",
        TokenKind::Gt        => ">",
        _ => "token",
    }
}

fn parse_use_path(path: &str, alias: Option<String>) -> Option<ImportKind> {
    let arrow = " -> ";

    if path.starts_with("bytes") && path.contains(arrow) {
        let rest = path.splitn(2, arrow).nth(1)?.trim();
        let (name, ver) = split_name_ver(rest);
        return Some(ImportKind::BytesRepo { name, version: ver, alias });
    }
    if path.starts_with("python") && path.contains(arrow) {
        let rest = path.splitn(2, arrow).nth(1)?.trim();
        let (name, ver) = split_name_ver(rest);
        return Some(ImportKind::Python { name, version: ver, alias });
    }
    if path.starts_with("std") && path.contains(arrow) {
        let parts: Vec<String> = path.split(arrow)
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty() && s != "std")
        .collect();
        if !parts.is_empty() { return Some(ImportKind::Std { path: parts, alias }); }
    }
    if path.starts_with("core") && path.contains(arrow) {
        let parts: Vec<String> = path.split(arrow)
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty() && s != "core")
        .collect();
        if !parts.is_empty() { return Some(ImportKind::Core { path: parts, alias }); }
    }
    if path.starts_with("vira") && path.contains(arrow) {
        let rest = path.splitn(2, arrow).nth(1)?.trim();
        let (name, ver) = split_name_ver(rest);
        return Some(ImportKind::Vira { name, version: ver, alias });
    }
    if path.starts_with("github") && path.contains(arrow) {
        let name = path.split(arrow).nth(1)?.trim().to_string();
        return Some(ImportKind::Github { name, alias });
    }
    if path.starts_with("github.com/") || path.starts_with("gitlab.com/") {
        return Some(ImportKind::Github { name: path.to_string(), alias });
    }
    if let Some(rest) = path.strip_prefix("std:") {
        let parts: Vec<String> = rest.split("::").map(|s| s.to_string()).collect();
        return Some(ImportKind::Std { path: parts, alias });
    }
    None
}

fn split_name_ver(s: &str) -> (String, Option<String>) {
    if let Some(idx) = s.rfind('/') {
        let n = &s[..idx]; let v = &s[idx + 1..];
        if v.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
            return (n.to_string(), Some(v.to_string()));
        }
    }
    (s.to_string(), None)
}
