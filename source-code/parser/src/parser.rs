use crate::ast::*;
use crate::lexer::{Spanned, Token, lex};
use std::fmt;

// ─── Błędy parsowania ──────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: crate::ast::Span,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Błąd składni w linii {}:{} - {}",
            self.span.line, self.span.col, self.message
        )
    }
}

impl std::error::Error for ParseError {}

// ─── Parser ────────────────────────────────────────────────────────────────

pub struct Parser {
    tokens: Vec<Spanned<Token>>,
    pos: usize,
    source: String,
}

impl Parser {
    pub fn new(tokens: Vec<Spanned<Token>>, source: String) -> Self {
        Self { tokens, pos: 0, source }
    }

    // ── Narzędzia ──────────────────────────────────────────────────────────

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|s| &s.inner)
    }

    fn peek2(&self) -> Option<&Token> {
        self.tokens.get(self.pos + 1).map(|s| &s.inner)
    }

    fn advance(&mut self) -> Option<&Spanned<Token>> {
        let tok = self.tokens.get(self.pos);
        self.pos += 1;
        tok
    }

    fn current_span(&self) -> crate::ast::Span {
        self.tokens.get(self.pos)
        .map(|s| crate::ast::Span { start: s.span.start, end: s.span.end, line: 0, col: 0 })
        .unwrap_or_default()
    }

    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Some(Token::Newline)) {
            self.advance();
        }
    }

    fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
        self.skip_newlines();
        match self.peek() {
            Some(tok) if std::mem::discriminant(tok) == std::mem::discriminant(expected) => {
                self.advance();
                Ok(())
            }
            Some(tok) => Err(ParseError {
                message: format!("Oczekiwano {:?}, znaleziono {:?}", expected, tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: format!("Oczekiwano {:?}, ale osiągnięto koniec pliku", expected),
                        span: self.current_span(),
            }),
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        self.skip_newlines();
        match self.peek() {
            Some(Token::Ident(_)) => {
                if let Some(s) = self.advance() {
                    if let Token::Ident(name) = &s.inner {
                        return Ok(name.clone());
                    }
                }
                unreachable!()
            }
            Some(tok) => Err(ParseError {
                message: format!("Oczekiwano identyfikatora, znaleziono {:?}", tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: "Oczekiwano identyfikatora, ale osiągnięto koniec pliku".into(),
                        span: self.current_span(),
            }),
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    // ── Parsowanie modułu ─────────────────────────────────────────────────

    pub fn parse_module(&mut self, name: &str) -> Result<Module, Vec<ParseError>> {
        let mut module = Module::new(name, self.source.clone());
        let mut errors = Vec::new();

        while !self.at_end() {
            self.skip_newlines();
            if self.at_end() { break; }

            match self.parse_decl() {
                Ok(decl) => module.decls.push(decl),
                Err(e) => {
                    errors.push(e);
                    // Recovery: przeskocz do następnej linii / ]
                    self.recover();
                }
            }
        }

        if errors.is_empty() { Ok(module) } else { Err(errors) }
    }

    fn recover(&mut self) {
        while !self.at_end() {
            match self.peek() {
                Some(Token::Newline)
                | Some(Token::Fn)
                | Some(Token::Class)
                | Some(Token::Enum)
                | Some(Token::Trait)
                | Some(Token::Impl) => break,
                _ => { self.advance(); }
            }
        }
    }

    // ── Deklaracje ────────────────────────────────────────────────────────

    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        self.skip_newlines();

        // Atrybuty
        let mut attrs = Vec::new();
        while matches!(self.peek(), Some(Token::Attribute(_))) {
            if let Some(s) = self.advance() {
                if let Token::Attribute(content) = &s.inner {
                    attrs.push(Attribute { content: content.clone(), span: Span::dummy() });
                }
            }
            self.skip_newlines();
        }

        // Widoczność
        let vis = if matches!(self.peek(), Some(Token::Pub)) {
            self.advance();
            Vis::Public
        } else {
            Vis::Private
        };

        match self.peek() {
            Some(Token::Fn) => self.parse_fn(vis, attrs),
            Some(Token::Class) => self.parse_class(vis, attrs),
            Some(Token::Enum) => self.parse_enum(vis, attrs),
            Some(Token::Trait) => self.parse_trait(vis),
            Some(Token::Impl) => self.parse_impl(),
            Some(Token::Const) => self.parse_const(vis),
            Some(Token::Type) => self.parse_type_alias(vis),
            Some(Token::Hash) => self.parse_import(),
            Some(Token::ScriptOpen) => self.parse_script_section(),
            Some(Token::Let) => {
                // Globalna stała let
                let stmt = self.parse_let()?;
                Ok(Decl::Const {
                    vis,
                    name: match &stmt {
                        Stmt::Let { name, .. } => name.clone(),
                   _ => unreachable!(),
                    },
                    ty: match &stmt {
                        Stmt::Let { ty, .. } => ty.clone().unwrap_or(Ty::Infer),
                   _ => unreachable!(),
                    },
                    value: match stmt {
                        Stmt::Let { value, .. } => value.unwrap_or(Box::new(Expr::Nil)),
                   _ => unreachable!(),
                    },
                    span: Span::dummy(),
                })
            }
            Some(tok) => Err(ParseError {
                message: format!("Nieoczekiwany token na poziomie modułu: {:?}", tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: "Nieoczekiwany koniec pliku".into(),
                        span: Span::dummy(),
            }),
        }
    }

    // ── Import: # <bytes/std_io//version:1.0> ─────────────────────────────

    fn parse_import(&mut self) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.expect(&Token::Hash)?;
        self.expect(&Token::Lt)?;

        // Czytamy zawartość aż do >
        let mut raw = String::new();
        while !matches!(self.peek(), Some(Token::Gt) | None) {
            if let Some(s) = self.advance() {
                match &s.inner {
                    Token::Ident(n) => raw.push_str(n),
                    Token::Slash => raw.push('/'),
                    Token::Dot => raw.push('.'),
                    Token::Minus => raw.push('-'),
                    Token::Colon => raw.push(':'),
                    _ => {}
                }
            }
        }
        self.expect(&Token::Gt)?;

        // Parsujemy: bytes/name lub core/name, opcjonalnie //version:X
        let (source_str, rest) = if let Some(idx) = raw.find('/') {
            (&raw[..idx], &raw[idx+1..])
        } else {
            (raw.as_str(), "")
        };

        let source = if source_str == "bytes" {
            ImportSource::Bytes
        } else {
            ImportSource::Core
        };

        let (name, version) = if let Some(idx) = rest.find("//version:") {
            (rest[..idx].to_string(), Some(rest[idx+10..].to_string()))
        } else {
            (rest.to_string(), None)
        };

        Ok(Decl::Import(ImportDecl { source, name, version, alias: None, span }))
    }

    // ── fn nazwa[generyki](params) -> Ty [ body ] ─────────────────────────

    fn parse_fn(&mut self, vis: Vis, attrs: Vec<Attribute>) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // fn

        let name = self.expect_ident()?;
        let generics = self.parse_generics()?;
        let params = self.parse_params()?;

        let return_ty = if matches!(self.peek(), Some(Token::Arrow)) {
            self.advance();
            self.parse_ty()?
        } else {
            Ty::Void
        };

        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        let body = self.parse_body()?;
        self.expect(&Token::RBracket)?;

        Ok(Decl::Function { vis, attrs, name, generics, params, return_ty, body, span })
    }

    // ── Claas Nazwa[G] impl Trait1, Trait2 [ fields + methods ] ──────────

    fn parse_class(&mut self, vis: Vis, attrs: Vec<Attribute>) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // Claas

        let name = self.expect_ident()?;
        let generics = self.parse_generics()?;

        let mut traits_impl = Vec::new();
        if matches!(self.peek(), Some(Token::Impl)) {
            self.advance();
            loop {
                traits_impl.push(self.expect_ident()?);
                if !matches!(self.peek(), Some(Token::Comma)) { break; }
                self.advance();
            }
        }

        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        self.skip_newlines();

        let mut fields = Vec::new();
        let mut methods = Vec::new();

        while !matches!(self.peek(), Some(Token::RBracket) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RBracket) | None) { break; }

            let item_attrs = self.parse_attrs();
            let item_vis = if matches!(self.peek(), Some(Token::Pub)) {
                self.advance(); Vis::Public
            } else {
                Vis::Private
            };

            if matches!(self.peek(), Some(Token::Fn)) {
                let method = self.parse_fn(item_vis, item_attrs)?;
                methods.push(method);
            } else {
                // Pole:  [mut] nazwa: Ty [= default]
                let mutable = if matches!(self.peek(), Some(Token::Mut)) {
                    self.advance(); true
                } else { false };

                let fname = self.expect_ident()?;
                self.expect(&Token::Colon)?;
                let ty = self.parse_ty()?;
                let default = if matches!(self.peek(), Some(Token::Eq)) {
                    self.advance();
                    Some(Box::new(self.parse_expr()?))
                } else { None };

                fields.push(Field {
                    name: fname, ty, mutable,
                    vis: item_vis, default,
                    attrs: item_attrs,
                    span: Span::dummy(),
                });
                self.skip_newlines();
            }
        }

        self.expect(&Token::RBracket)?;
        Ok(Decl::Class { vis, attrs, name, generics, fields, methods, traits_impl, span })
    }

    // ── enum Nazwa [ A, B(Ty), C(Ty, Ty) ] ───────────────────────────────

    fn parse_enum(&mut self, vis: Vis, attrs: Vec<Attribute>) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // enum

        let name = self.expect_ident()?;
        let generics = self.parse_generics()?;
        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        self.skip_newlines();

        let mut variants = Vec::new();
        while !matches!(self.peek(), Some(Token::RBracket) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RBracket) | None) { break; }

            let vname = self.expect_ident()?;
            let mut fields = Vec::new();

            if matches!(self.peek(), Some(Token::LParen)) {
                self.advance();
                while !matches!(self.peek(), Some(Token::RParen) | None) {
                    fields.push(self.parse_ty()?);
                    if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
                }
                self.expect(&Token::RParen)?;
            }

            variants.push(EnumVariant { name: vname, fields, span: Span::dummy() });
            if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
            self.skip_newlines();
        }

        self.expect(&Token::RBracket)?;
        Ok(Decl::Enum { vis, attrs, name, generics, variants, span })
    }

    // ── trait Nazwa [ elementy ] ──────────────────────────────────────────

    fn parse_trait(&mut self, vis: Vis) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // trait

        let name = self.expect_ident()?;
        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        self.skip_newlines();

        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBracket) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RBracket) | None) { break; }

            let item_attrs = self.parse_attrs();
            if matches!(self.peek(), Some(Token::Fn)) {
                self.advance(); // fn
                let fname = self.expect_ident()?;
                let params = self.parse_params()?;
                let return_ty = if matches!(self.peek(), Some(Token::Arrow)) {
                    self.advance();
                    self.parse_ty()?
                } else { Ty::Void };

                let default_body = if matches!(self.peek(), Some(Token::LBracket)) {
                    self.advance();
                    let body = self.parse_body()?;
                    self.expect(&Token::RBracket)?;
                    Some(body)
                } else { None };

                items.push(TraitItem { name: fname, params, return_ty, default_body, attrs: item_attrs, span: Span::dummy() });
            }
            self.skip_newlines();
        }

        self.expect(&Token::RBracket)?;
        Ok(Decl::Trait { vis, name, items, span })
    }

    // ── impl [Trait dla] Klasa [ ... ] ───────────────────────────────────

    fn parse_impl(&mut self) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // impl

        let first = self.expect_ident()?;
        let (trait_name, target) = if matches!(self.peek(), Some(Token::For)) {
            self.advance();
            (Some(first), self.expect_ident()?)
        } else {
            (None, first)
        };

        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        self.skip_newlines();

        let mut items = Vec::new();
        while !matches!(self.peek(), Some(Token::RBracket) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RBracket) | None) { break; }

            let attrs = self.parse_attrs();
            let vis = if matches!(self.peek(), Some(Token::Pub)) {
                self.advance(); Vis::Public
            } else { Vis::Private };

            if matches!(self.peek(), Some(Token::Fn)) {
                items.push(self.parse_fn(vis, attrs)?);
            } else {
                break;
            }
        }

        self.expect(&Token::RBracket)?;
        Ok(Decl::Impl { trait_name, target, items, span })
    }

    // ── const NAZWA: Ty = wartość ─────────────────────────────────────────

    fn parse_const(&mut self, vis: Vis) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // const
        let name = self.expect_ident()?;
        self.expect(&Token::Colon)?;
        let ty = self.parse_ty()?;
        self.expect(&Token::Eq)?;
        let value = self.parse_expr()?;
        Ok(Decl::Const { vis, name, ty, value: Box::new(value), span })
    }

    // ── type Nowy = Stary ─────────────────────────────────────────────────

    fn parse_type_alias(&mut self, vis: Vis) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // type
        let name = self.expect_ident()?;
        self.expect(&Token::Eq)?;
        let ty = self.parse_ty()?;
        Ok(Decl::TypeAlias { vis, name, ty, span })
    }

    // ── Sekcja skryptowa --- ──────────────────────────────────────────────

    fn parse_script_section(&mut self) -> Result<Decl, ParseError> {
        let span = self.current_span();
        self.advance(); // ---
        self.skip_newlines();

        let mut commands = Vec::new();
        while !matches!(self.peek(), Some(Token::ScriptOpen) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::ScriptOpen) | None) { break; }
            commands.push(self.parse_script_cmd()?);
        }

        if matches!(self.peek(), Some(Token::ScriptOpen)) {
            self.advance(); // zamykający ---
        }

        Ok(Decl::ScriptSection(ScriptSection { commands, span }))
    }

    fn parse_script_cmd(&mut self) -> Result<ScriptCmd, ParseError> {
        self.skip_newlines();
        match self.peek() {
            Some(Token::Comment(c)) => {
                let c = c.clone();
                self.advance();
                Ok(ScriptCmd::Comment(c))
            }
            Some(Token::Gt) => {
                self.advance();
                // Sprawdź czy >>> lub >>
                if matches!(self.peek(), Some(Token::Gt)) {
                    self.advance();
                    if matches!(self.peek(), Some(Token::Gt)) {
                        self.advance();
                        // >>>  izolowana komenda
                        let (cmd, args) = self.parse_shell_call()?;
                        return Ok(ScriptCmd::Isolated { cmd, args, span: Span::dummy() });
                    }
                    // >>  z zmiennymi
                    let (cmd, args) = self.parse_shell_call()?;
                    return Ok(ScriptCmd::WithVars { cmd, args, env: vec![], span: Span::dummy() });
                }
                // > zwykła komenda
                let (cmd, args) = self.parse_shell_call()?;
                Ok(ScriptCmd::Shell { cmd, args, span: Span::dummy() })
            }
            Some(Token::Let) => {
                self.advance();
                let name = self.expect_ident()?;
                self.expect(&Token::Eq)?;
                let value = self.parse_script_arg()?;
                Ok(ScriptCmd::Let { name, value, span: Span::dummy() })
            }
            Some(Token::Ident(n)) if n == "deps" => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let mut pkgs = Vec::new();
                while !matches!(self.peek(), Some(Token::RBracket) | None) {
                    pkgs.push(self.expect_ident()?);
                    if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
                }
                self.expect(&Token::RBracket)?;
                Ok(ScriptCmd::Deps { packages: pkgs, span: Span::dummy() })
            }
            Some(tok) => Err(ParseError {
                message: format!("Nieoczekiwany token w sekcji skryptowej: {:?}", tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: "Nieoczekiwany koniec sekcji skryptowej".into(),
                        span: Span::dummy(),
            }),
        }
    }

    fn parse_shell_call(&mut self) -> Result<(String, Vec<ScriptArg>), ParseError> {
        let cmd = self.expect_ident()?;
        let mut args = Vec::new();
        // Czytamy argumenty aż do nowej linii
        while !matches!(self.peek(), Some(Token::Newline) | None) {
            args.push(self.parse_script_arg()?);
        }
        Ok((cmd, args))
    }

    fn parse_script_arg(&mut self) -> Result<ScriptArg, ParseError> {
        match self.peek() {
            Some(Token::StringLit(_)) => {
                if let Some(s) = self.advance() {
                    if let Token::StringLit(v) = &s.inner {
                        return Ok(ScriptArg::Literal(v.clone()));
                    }
                }
                unreachable!()
            }
            Some(Token::Dollar) => {
                self.advance();
                let name = self.expect_ident()?;
                Ok(ScriptArg::Var(name))
            }
            _ => {
                let name = self.expect_ident()?;
                Ok(ScriptArg::Literal(name))
            }
        }
    }

    // ── Typy ──────────────────────────────────────────────────────────────

    fn parse_ty(&mut self) -> Result<Ty, ParseError> {
        self.skip_newlines();
        match self.peek().cloned() {
            Some(Token::TyInt) => { self.advance(); Ok(Ty::Int) }
            Some(Token::TyFloat) => { self.advance(); Ok(Ty::Float) }
            Some(Token::TyBool) => { self.advance(); Ok(Ty::Bool) }
            Some(Token::TyStr) => { self.advance(); Ok(Ty::Str) }
            Some(Token::TyChar) => { self.advance(); Ok(Ty::Char) }
            Some(Token::TyVoid) => { self.advance(); Ok(Ty::Void) }
            Some(Token::TyList) => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let inner = self.parse_ty()?;
                self.expect(&Token::RBracket)?;
                Ok(Ty::List(Box::new(inner)))
            }
            Some(Token::TyMap) => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let k = self.parse_ty()?;
                self.expect(&Token::Comma)?;
                let v = self.parse_ty()?;
                self.expect(&Token::RBracket)?;
                Ok(Ty::Map(Box::new(k), Box::new(v)))
            }
            Some(Token::TyOption) => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let inner = self.parse_ty()?;
                self.expect(&Token::RBracket)?;
                Ok(Ty::Option(Box::new(inner)))
            }
            Some(Token::TyResult) => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let ok = self.parse_ty()?;
                self.expect(&Token::Comma)?;
                let err = self.parse_ty()?;
                self.expect(&Token::RBracket)?;
                Ok(Ty::Result(Box::new(ok), Box::new(err)))
            }
            Some(Token::TyArc) => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let inner = self.parse_ty()?;
                self.expect(&Token::RBracket)?;
                Ok(Ty::Arc(Box::new(inner)))
            }
            Some(Token::TyBox) => {
                self.advance();
                self.expect(&Token::LBracket)?;
                let inner = self.parse_ty()?;
                self.expect(&Token::RBracket)?;
                Ok(Ty::Box(Box::new(inner)))
            }
            Some(Token::Fn) => {
                self.advance();
                self.expect(&Token::LParen)?;
                let mut params = Vec::new();
                while !matches!(self.peek(), Some(Token::RParen) | None) {
                    params.push(self.parse_ty()?);
                    if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
                }
                self.expect(&Token::RParen)?;
                self.expect(&Token::Arrow)?;
                let ret = self.parse_ty()?;
                Ok(Ty::Fn(params, Box::new(ret)))
            }
            Some(Token::Ident(name)) => {
                self.advance();
                if matches!(self.peek(), Some(Token::LBracket)) {
                    self.advance();
                    let mut args = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBracket) | None) {
                        args.push(self.parse_ty()?);
                        if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
                    }
                    self.expect(&Token::RBracket)?;
                    Ok(Ty::Generic(name, args))
                } else {
                    Ok(Ty::Named(name))
                }
            }
            Some(tok) => Err(ParseError {
                message: format!("Oczekiwano typu, znaleziono {:?}", tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: "Oczekiwano typu, ale osiągnięto koniec pliku".into(),
                        span: Span::dummy(),
            }),
        }
    }

    // ── Generyki: [T, U] ──────────────────────────────────────────────────

    fn parse_generics(&mut self) -> Result<Vec<String>, ParseError> {
        if !matches!(self.peek(), Some(Token::Lt)) {
            return Ok(Vec::new());
        }
        self.advance(); // <
        let mut gs = Vec::new();
        while !matches!(self.peek(), Some(Token::Gt) | None) {
            gs.push(self.expect_ident()?);
            if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
        }
        self.expect(&Token::Gt)?;
        Ok(gs)
    }

    // ── Parametry: (nazwa: Ty, ...) ───────────────────────────────────────

    fn parse_params(&mut self) -> Result<Vec<Param>, ParseError> {
        self.expect(&Token::LParen)?;
        let mut params = Vec::new();

        while !matches!(self.peek(), Some(Token::RParen) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RParen) | None) { break; }

            let mutable = if matches!(self.peek(), Some(Token::Mut)) {
                self.advance(); true
            } else { false };

            let name = if matches!(self.peek(), Some(Token::SelfKw)) {
                self.advance();
                "self".to_string()
            } else {
                self.expect_ident()?
            };

            let ty = if matches!(self.peek(), Some(Token::Colon)) {
                self.advance();
                self.parse_ty()?
            } else {
                Ty::Infer
            };

            let default = if matches!(self.peek(), Some(Token::Eq)) {
                self.advance();
                Some(Box::new(self.parse_expr()?))
            } else { None };

            params.push(Param { name, ty, mutable, default, span: Span::dummy() });

            if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
        }

        self.expect(&Token::RParen)?;
        Ok(params)
    }

    // ── Ciało funkcji: lista instrukcji ───────────────────────────────────

    fn parse_body(&mut self) -> Result<Vec<Stmt>, ParseError> {
        let mut stmts = Vec::new();
        self.skip_newlines();

        while !matches!(self.peek(), Some(Token::RBracket) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RBracket) | None) { break; }
            stmts.push(self.parse_stmt()?);
            // Opcjonalny separator
            if matches!(self.peek(), Some(Token::Semicolon)) { self.advance(); }
        }

        Ok(stmts)
    }

    // ── Instrukcje ────────────────────────────────────────────────────────

    fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.skip_newlines();

        match self.peek() {
            Some(Token::Let) => self.parse_let(),
            Some(Token::Return) => {
                self.advance();
                let val = if !matches!(self.peek(), Some(Token::Newline | Token::RBracket | Token::Semicolon) | None) {
                    Some(Box::new(self.parse_expr()?))
                } else { None };
                Ok(Stmt::Return(val))
            }
            Some(Token::Break) => {
                self.advance();
                let val = if !matches!(self.peek(), Some(Token::Newline | Token::RBracket | Token::Semicolon) | None) {
                    Some(Box::new(self.parse_expr()?))
                } else { None };
                Ok(Stmt::Break(val))
            }
            Some(Token::Next) => {
                self.advance();
                Ok(Stmt::Next)
            }
            Some(Token::Raise) => {
                self.advance();
                let val = self.parse_expr()?;
                Ok(Stmt::Raise(Box::new(val)))
            }
            Some(Token::While) => self.parse_while(),
            Some(Token::For) => self.parse_for(),
            Some(Token::Rescue) => self.parse_rescue(),
            _ => {
                // Wyrażenie lub przypisanie
                let expr = self.parse_expr()?;
                // Sprawdzamy czy to przypisanie
                if matches!(self.peek(), Some(Token::Eq)) {
                    self.advance();
                    let value = self.parse_expr()?;
                    return Ok(Stmt::Assign {
                        target: Box::new(expr),
                              value: Box::new(value),
                              span: Span::dummy(),
                    });
                }
                Ok(Stmt::Expr(expr))
            }
        }
    }

    fn parse_let(&mut self) -> Result<Stmt, ParseError> {
        let span = self.current_span();
        self.advance(); // let
        let mutable = if matches!(self.peek(), Some(Token::Mut)) {
            self.advance(); true
        } else { false };

        let name = self.expect_ident()?;
        let ty = if matches!(self.peek(), Some(Token::Colon)) {
            self.advance();
            Some(self.parse_ty()?)
        } else { None };

        let value = if matches!(self.peek(), Some(Token::Eq)) {
            self.advance();
            Some(Box::new(self.parse_expr()?))
        } else { None };

        Ok(Stmt::Let { name, ty, mutable, value, span })
    }

    fn parse_while(&mut self) -> Result<Stmt, ParseError> {
        let span = self.current_span();
        self.advance(); // while
        let cond = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        let body = self.parse_body()?;
        self.expect(&Token::RBracket)?;
        Ok(Stmt::While { cond: Box::new(cond), body, span })
    }

    fn parse_for(&mut self) -> Result<Stmt, ParseError> {
        let span = self.current_span();
        self.advance(); // for
        let var = self.expect_ident()?;
        self.expect(&Token::In)?;
        let iterable = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        let body = self.parse_body()?;
        self.expect(&Token::RBracket)?;
        Ok(Stmt::For { var, iterable: Box::new(iterable), body, span })
    }

    fn parse_rescue(&mut self) -> Result<Stmt, ParseError> {
        let span = self.current_span();
        // rescue [ body ] rescue Type => e [ handler ] ensure [ cleanup ]
        // Parsujemy uproszczoną wersję
        self.advance(); // rescue (pierwsze użycie jako blok begin)
        self.expect(&Token::LBracket)?;
        let body = self.parse_body()?;
        self.expect(&Token::RBracket)?;

        let mut handlers = Vec::new();
        while matches!(self.peek(), Some(Token::Rescue)) {
            self.advance();
            let error_type = match self.peek() {
                Some(Token::Ident(_)) => Some(self.expect_ident()?),
                _ => None,
            };
            let binding = if matches!(self.peek(), Some(Token::FatArrow)) {
                self.advance();
                Some(self.expect_ident()?)
            } else { None };
            self.expect(&Token::LBracket)?;
            let hbody = self.parse_body()?;
            self.expect(&Token::RBracket)?;
            handlers.push(RescueHandler { error_type, binding, body: hbody, span: Span::dummy() });
        }

        let ensure = if matches!(self.peek(), Some(Token::Ensure)) {
            self.advance();
            self.expect(&Token::LBracket)?;
            let e = self.parse_body()?;
            self.expect(&Token::RBracket)?;
            e
        } else { Vec::new() };

        Ok(Stmt::Rescue { body, handlers, ensure, span })
    }

    // ── Wyrażenia (Pratt parser) ──────────────────────────────────────────

    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_assignment()
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParseError> {
        let lhs = self.parse_or()?;
        match self.peek() {
            Some(Token::PlusEq | Token::MinusEq | Token::StarEq | Token::SlashEq) => {
                let op = match self.peek().unwrap() {
                    Token::PlusEq => BinOp::AddAssign,
                    Token::MinusEq => BinOp::SubAssign,
                    Token::StarEq => BinOp::MulAssign,
                    Token::SlashEq => BinOp::DivAssign,
                    _ => unreachable!(),
                };
                self.advance();
                let rhs = self.parse_or()?;
                Ok(Expr::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), span: Span::dummy() })
            }
            _ => Ok(lhs),
        }
    }

    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_and()?;
        while matches!(self.peek(), Some(Token::OrOr | Token::Or)) {
            self.advance();
            let rhs = self.parse_and()?;
            lhs = Expr::BinOp { op: BinOp::Or, lhs: Box::new(lhs), rhs: Box::new(rhs), span: Span::dummy() };
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_cmp()?;
        while matches!(self.peek(), Some(Token::AndAnd | Token::And)) {
            self.advance();
            let rhs = self.parse_cmp()?;
            lhs = Expr::BinOp { op: BinOp::And, lhs: Box::new(lhs), rhs: Box::new(rhs), span: Span::dummy() };
        }
        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_add()?;
        loop {
            let op = match self.peek() {
                Some(Token::EqEq) => BinOp::Eq,
                Some(Token::NotEq) => BinOp::NotEq,
                Some(Token::Lt) => BinOp::Lt,
                Some(Token::Gt) => BinOp::Gt,
                Some(Token::LtEq) => BinOp::LtEq,
                Some(Token::GtEq) => BinOp::GtEq,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_add()?;
            lhs = Expr::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), span: Span::dummy() };
        }
        Ok(lhs)
    }

    fn parse_add(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_mul()?;
        loop {
            let op = match self.peek() {
                Some(Token::Plus) => BinOp::Add,
                Some(Token::Minus) => BinOp::Sub,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_mul()?;
            lhs = Expr::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), span: Span::dummy() };
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Some(Token::Star) => BinOp::Mul,
                Some(Token::Slash) => BinOp::Div,
                Some(Token::Percent) => BinOp::Mod,
                Some(Token::StarStar) => BinOp::Pow,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_unary()?;
            lhs = Expr::BinOp { op, lhs: Box::new(lhs), rhs: Box::new(rhs), span: Span::dummy() };
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            Some(Token::Minus) => {
                self.advance();
                let e = self.parse_unary()?;
                Ok(Expr::UnaryOp { op: UnaryOp::Neg, expr: Box::new(e), span: Span::dummy() })
            }
            Some(Token::Not) => {
                self.advance();
                let e = self.parse_unary()?;
                Ok(Expr::UnaryOp { op: UnaryOp::Not, expr: Box::new(e), span: Span::dummy() })
            }
            Some(Token::Tilde) => {
                self.advance();
                let e = self.parse_unary()?;
                Ok(Expr::UnaryOp { op: UnaryOp::BitNot, expr: Box::new(e), span: Span::dummy() })
            }
            _ => self.parse_postfix(),
        }
    }

    fn parse_postfix(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_primary()?;

        loop {
            match self.peek() {
                Some(Token::Dot) => {
                    self.advance();
                    let field = self.expect_ident()?;
                    if matches!(self.peek(), Some(Token::LParen)) {
                        let args = self.parse_call_args()?;
                        expr = Expr::MethodCall { object: Box::new(expr), method: field, args, span: Span::dummy() };
                    } else {
                        expr = Expr::FieldAccess { object: Box::new(expr), field, span: Span::dummy() };
                    }
                }
                Some(Token::LBracket) => {
                    // Może być wywołanie przez nawiasy kwadratowe (indeks)
                    // Sprawdzamy czy to nie jest blok
                    self.advance();
                    let idx = self.parse_expr()?;
                    self.expect(&Token::RBracket)?;
                    expr = Expr::IndexAccess { object: Box::new(expr), index: Box::new(idx), span: Span::dummy() };
                }
                Some(Token::LParen) => {
                    let args = self.parse_call_args()?;
                    expr = Expr::Call { callee: Box::new(expr), args, span: Span::dummy() };
                }
                Some(Token::Question) => {
                    self.advance();
                    expr = Expr::Try(Box::new(expr));
                }
                Some(Token::As) => {
                    self.advance();
                    let ty = self.parse_ty()?;
                    expr = Expr::Cast { expr: Box::new(expr), ty, span: Span::dummy() };
                }
                Some(Token::Is) => {
                    self.advance();
                    let ty = self.parse_ty()?;
                    expr = Expr::TypeCheck { expr: Box::new(expr), ty, span: Span::dummy() };
                }
                _ => break,
            }
        }

        Ok(expr)
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        self.expect(&Token::LParen)?;
        let mut args = Vec::new();
        while !matches!(self.peek(), Some(Token::RParen) | None) {
            args.push(self.parse_expr()?);
            if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
        }
        self.expect(&Token::RParen)?;
        Ok(args)
    }

    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        self.skip_newlines();
        match self.peek().cloned() {
            // Literały
            Some(Token::IntLit(n)) => {

                self.advance();
                Ok(Expr::Int(n))
            }
            Some(Token::FloatLit(f)) => {
                self.advance();
                Ok(Expr::Float(f))
            }
            Some(Token::True) => { self.advance(); Ok(Expr::Bool(true)) }
            Some(Token::False) => { self.advance(); Ok(Expr::Bool(false)) }
            Some(Token::Nil) => { self.advance(); Ok(Expr::Nil) }
            Some(Token::StringLit(s)) => { self.advance(); Ok(Expr::Str(s)) }
            Some(Token::CharLit(c)) => { self.advance(); Ok(Expr::Char(c)) }
            Some(Token::SelfKw) => { self.advance(); Ok(Expr::SelfExpr) }

            // write "tekst"
            Some(Token::Write) => {
                let span = self.current_span();
                self.advance();
                let mut args = Vec::new();
                while !matches!(self.peek(), Some(Token::Newline | Token::Semicolon | Token::RBracket) | None) {
                    args.push(self.parse_expr()?);
                    if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
                }
                Ok(Expr::Write { args, newline: true, span })
            }

            // Blok [ ... ]
            Some(Token::LBracket) => {
                self.advance();
                // Lista lub blok?
                if matches!(self.peek(), Some(Token::RBracket)) {
                    self.advance();
                    return Ok(Expr::List(Vec::new()));
                }
                let stmts = self.parse_body()?;
                self.expect(&Token::RBracket)?;
                Ok(Expr::Block(stmts))
            }

            // Grupowanie (a + b)
            Some(Token::LParen) => {
                self.advance();
                let e = self.parse_expr()?;
                self.expect(&Token::RParen)?;
                Ok(e)
            }

            // if
            Some(Token::If) => self.parse_if_expr(),

            // match
            Some(Token::Match) => self.parse_match_expr(),

            // new Klasa(args)
            Some(Token::New) => {
                let span = self.current_span();
                self.advance();
                let class = self.expect_ident()?;
                self.expect(&Token::LParen)?;
                let mut args = Vec::new();
                while !matches!(self.peek(), Some(Token::RParen) | None) {
                    // Sprawdź czy nazwany argument
                    if matches!(self.peek(), Some(Token::Ident(_))) && matches!(self.peek2(), Some(Token::Colon)) {
                        let name = self.expect_ident()?;
                        self.advance(); // :
                        let val = self.parse_expr()?;
                        args.push((Some(name), val));
                    } else {
                        args.push((None, self.parse_expr()?));
                    }
                    if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
                }
                self.expect(&Token::RParen)?;
                Ok(Expr::New { class, args, span })
            }

            // Arena alloc: :: nazwa [size] [ body ]
            Some(Token::DoubleColon) => {
                let span = self.current_span();
                self.advance();
                let name = self.expect_ident()?;
                self.expect(&Token::LBracket)?;
                let size = self.parse_expr()?;
                self.expect(&Token::RBracket)?;
                self.expect(&Token::LBracket)?;
                let body = self.parse_body()?;
                self.expect(&Token::RBracket)?;
                Ok(Expr::ArenaBlock { name, size: Box::new(size), body, span })
            }

            // Identyfikator
            Some(Token::Ident(name)) => {
                self.advance();
                Ok(Expr::Var(name))
            }

            Some(tok) => Err(ParseError {
                message: format!("Nieoczekiwany token w wyrażeniu: {:?}", tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: "Nieoczekiwany koniec pliku w wyrażeniu".into(),
                        span: Span::dummy(),
            }),
        }
    }

    fn parse_if_expr(&mut self) -> Result<Expr, ParseError> {
        let span = self.current_span();
        self.advance(); // if
        let cond = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        let then_body = self.parse_body()?;
        self.expect(&Token::RBracket)?;

        let mut elsif = Vec::new();
        while matches!(self.peek(), Some(Token::Elsif)) {
            self.advance();
            let ec = self.parse_expr()?;
            self.skip_newlines();
            self.expect(&Token::LBracket)?;
            let eb = self.parse_body()?;
            self.expect(&Token::RBracket)?;
            elsif.push((ec, Expr::Block(eb)));
        }

        let otherwise = if matches!(self.peek(), Some(Token::Else)) {
            self.advance();
            self.skip_newlines();
            self.expect(&Token::LBracket)?;
            let b = self.parse_body()?;
            self.expect(&Token::RBracket)?;
            Some(Box::new(Expr::Block(b)))
        } else { None };

        Ok(Expr::If {
            cond: Box::new(cond),
           then: Box::new(Expr::Block(then_body)),
           elsif,
           otherwise,
           span,
        })
    }

    fn parse_match_expr(&mut self) -> Result<Expr, ParseError> {
        let span = self.current_span();
        self.advance(); // match
        let value = self.parse_expr()?;
        self.skip_newlines();
        self.expect(&Token::LBracket)?;
        self.skip_newlines();

        let mut arms = Vec::new();
        while !matches!(self.peek(), Some(Token::RBracket) | None) {
            self.skip_newlines();
            if matches!(self.peek(), Some(Token::RBracket) | None) { break; }

            let pattern = self.parse_pattern()?;
            let guard = if matches!(self.peek(), Some(Token::If)) {
                self.advance();
                Some(self.parse_expr()?)
            } else { None };

            self.expect(&Token::FatArrow)?;
            let body = self.parse_expr()?;
            if matches!(self.peek(), Some(Token::Comma)) { self.advance(); }
            self.skip_newlines();

            arms.push(MatchArm { pattern, guard, body, span: Span::dummy() });
        }

        self.expect(&Token::RBracket)?;
        Ok(Expr::Match { value: Box::new(value), arms, span })
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        match self.peek().cloned() {
            Some(Token::Ident(n)) if n == "_" => { self.advance(); Ok(Pattern::Wildcard) }
            Some(Token::IntLit(n)) => { self.advance(); Ok(Pattern::Int(n)) }
            Some(Token::FloatLit(f)) => { self.advance(); Ok(Pattern::Float(f)) }
            Some(Token::True) => { self.advance(); Ok(Pattern::Bool(true)) }
            Some(Token::False) => { self.advance(); Ok(Pattern::Bool(false)) }
            Some(Token::Nil) => { self.advance(); Ok(Pattern::Nil) }
            Some(Token::StringLit(s)) => { self.advance(); Ok(Pattern::Str(s)) }
            Some(Token::Ident(n)) => { self.advance(); Ok(Pattern::Var(n)) }
            Some(tok) => Err(ParseError {
                message: format!("Nieoczekiwany token we wzorcu: {:?}", tok),
                             span: self.current_span(),
            }),
            None => Err(ParseError {
                message: "EOF we wzorcu".into(),
                        span: Span::dummy(),
            }),
        }
    }

    // ── Atrybuty ──────────────────────────────────────────────────────────

    fn parse_attrs(&mut self) -> Vec<Attribute> {
        let mut attrs = Vec::new();
        while matches!(self.peek(), Some(Token::Attribute(_))) {
            if let Some(s) = self.advance() {
                if let Token::Attribute(content) = &s.inner {
                    attrs.push(Attribute { content: content.clone(), span: Span::dummy() });
                }
            }
            self.skip_newlines();
        }
        attrs
    }
}

// ─── Publiczne API ────────────────────────────────────────────────────────

/// Parsuje kod źródłowy H# i zwraca moduł AST
pub fn parse(source: &str, name: &str) -> Result<Module, String> {
    let tokens = match lex(source) {
        Ok(t) => t,
        Err(errors) => {
            return Err(errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
            .join("\n"));
        }
    };

    let mut parser = Parser::new(tokens, source.to_string());
    parser.parse_module(name).map_err(|errors| {
        errors
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n")
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_fn() {
        let src = r#"
        fn powitaj(name: Str) -> Void [
        write "Cześć, " + name
        ]
        "#;
        let module = parse(src, "test").expect("parse failed");
        assert_eq!(module.decls.len(), 1);
        assert!(matches!(module.decls[0], Decl::Function { .. }));
    }

    #[test]
    fn test_parse_class() {
        let src = r#"
        Claas Osoba [
        imie: Str
        wiek: Int

        fn nowy(imie: Str, wiek: Int) -> Osoba [
        return new Osoba(imie: imie, wiek: wiek)
        ]
        ]
        "#;
        let module = parse(src, "test").expect("parse failed");
        assert_eq!(module.decls.len(), 1);
        assert!(matches!(module.decls[0], Decl::Class { .. }));
    }

    #[test]
    fn test_parse_import() {
        let src = r#"# <bytes/std_io//version:1.0>"#;
        let module = parse(src, "test").expect("parse failed");
        assert!(matches!(module.decls[0], Decl::Import(_)));
    }

    #[test]
    fn test_parse_let() {
        let src = r#"
        fn main() [
        let x: Int = 42
        let mut s: Str = "hello"
        write x
        ]
        "#;
        let module = parse(src, "test").expect("parse failed");
        assert!(matches!(module.decls[0], Decl::Function { .. }));
    }

    #[test]
    fn test_parse_match() {
        let src = r#"
        fn check(x: Int) -> Str [
        match x [
        0 => "zero",
        1 => "jeden",
        _ => "inne"
        ]
        ]
        "#;
        parse(src, "test").expect("parse failed");
    }
}
