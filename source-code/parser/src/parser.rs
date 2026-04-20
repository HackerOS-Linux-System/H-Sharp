use crate::ast::*;
use crate::error::{ParseError, ParseErrorKind, ErrorReporter};
use crate::lexer::{Token, TokenKind};
use crate::span::Span;

pub struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    #[allow(dead_code)] source: String,
    file: String,
    pub errors: ErrorReporter,
}

#[allow(dead_code)]
impl Parser {
    pub fn new(tokens: Vec<Token>, source: String, file: String) -> Self {
        // Filter out newlines for most parsing, but track them for block endings
        Self { tokens, pos: 0, source, file, errors: ErrorReporter::new() }
    }

    fn current(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or(self.tokens.last().unwrap())
    }

    fn peek(&self, offset: usize) -> &Token {
        self.tokens.get(self.pos + offset).unwrap_or(self.tokens.last().unwrap())
    }

    fn advance(&mut self) -> &Token {
        let t = &self.tokens[self.pos];
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn skip_newlines(&mut self) {
        while matches!(self.current().kind, TokenKind::Newline) {
            self.advance();
        }
    }

    fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.current().kind) == std::mem::discriminant(kind)
    }

    fn at_keyword(&self, kw: &TokenKind) -> bool {
        &self.current().kind == kw
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

    fn error(&self, msg: impl Into<String>, hints: Vec<String>) -> ParseError {
        let msg_str: String = msg.into();
        ParseError::new(
            ParseErrorKind::Custom(msg_str.clone()),
            self.current().span.clone(),
            msg_str,
            hints,
        )
    }

    // ── Public entry point ─────────────────────────────────────────────────────

    pub fn parse_module(&mut self) -> Module {
        let mut directives = Vec::new();
        let mut items = Vec::new();
        let mut imports = Vec::new();

        self.skip_newlines();

        while !matches!(self.current().kind, TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::EOF) { break; }

            // Directives
            if let TokenKind::Directive(s) = &self.current().kind.clone() {
                let span = self.current().span.clone();
                let s = s.clone();
                self.advance();
                directives.push(Directive {
                    kind: DirectiveKind::Dynamic,
                    value: s,
                    span,
                });
                continue;
            }
            if let TokenKind::FastDirective(s) = &self.current().kind.clone() {
                let span = self.current().span.clone();
                let s = s.clone();
                self.advance();
                directives.push(Directive {
                    kind: DirectiveKind::Fast,
                    value: s,
                    span,
                });
                continue;
            }

            // Imports
            if matches!(self.current().kind, TokenKind::Use) {
                match self.parse_import() {
                    Ok((kind, alias, span)) => imports.push((kind, alias, span)),
                    Err(e) => { self.errors.report(e); self.recover(); }
                }
                continue;
            }

            // Items
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(e) => { self.errors.report(e); self.recover(); }
            }
        }

        Module { file: self.file.clone(), directives, items, imports }
    }

    fn recover(&mut self) {
        // Skip until next statement boundary
        while !matches!(self.current().kind,
            TokenKind::EOF | TokenKind::Newline | TokenKind::Fn | TokenKind::Struct |
            TokenKind::Enum | TokenKind::Impl | TokenKind::Pub | TokenKind::Use) {
            self.advance();
        }
    }

    // ── Import ────────────────────────────────────────────────────────────────

    fn parse_import(&mut self) -> Result<(ImportKind, Option<String>, Span), ParseError> {
        let start = self.current().span.clone();
        self.advance(); // consume 'use'

        // Parse: use "std -> time -> clock" from "alias"
        // or:    use "vira -> pkgname/1.0" from "alias"
        // or:    use "github.com/user/repo" from "alias"
        let path_tok = if let TokenKind::StringLit(s) = &self.current().kind.clone() {
            let s = s.clone();
            self.advance();
            s
        } else {
            return Err(self.error(
                "expected use path string after `use`",
                vec![
                    r#"write: use "std -> io -> keyboard" from "kb""#.to_string(),
                    r#"or:    use "vira -> scanner/1.2" from "scanner""#.to_string(),
                    r#"or:    use "github.com/user/repo" from "repo""#.to_string(),
                ],
            ));
        };

        // Parse optional: from "alias"
        let alias = if matches!(self.current().kind, TokenKind::From) {
            self.advance();
            if let TokenKind::StringLit(a) = &self.current().kind.clone() {
                let a = a.clone();
                self.advance();
                Some(a)
            } else {
                return Err(self.error("expected alias string after `from`", vec![]));
            }
        } else {
            None
        };

        let span = start.merge(&self.current().span);
        let kind = parse_use_path(&path_tok, alias.clone()).ok_or_else(|| {
            ParseError::new(
                ParseErrorKind::Custom("invalid use path".into()),
                span.clone(),
                format!("cannot parse use path `{}`", path_tok),
                vec![
                    r#"valid forms: "std -> module -> sub", "vira -> pkg/1.0", "github.com/user/repo""#.to_string(),
                ],
            )
        })?;

        Ok((kind, alias, span))
    }

    // ── Items ─────────────────────────────────────────────────────────────────

    fn parse_item(&mut self) -> Result<Item, ParseError> {
        self.skip_newlines();
        let pub_ = if matches!(self.current().kind, TokenKind::Pub) {
            self.advance(); true
        } else { false };

        match &self.current().kind {
            TokenKind::Fn => self.parse_fn(pub_).map(Item::FnDef),
            TokenKind::Struct => self.parse_struct(pub_).map(Item::StructDef),
            TokenKind::Enum => self.parse_enum(pub_).map(Item::EnumDef),
            TokenKind::Trait => self.parse_trait(pub_).map(Item::TraitDef),
            TokenKind::Impl => self.parse_impl().map(Item::ImplBlock),
            TokenKind::Type => self.parse_type_alias(pub_).map(|ta| ta),
            TokenKind::Async => {
                // async fn — consume async, then parse as regular fn with is_async=true
                self.advance();
                let fn_def = self.parse_fn(pub_)?;
                Ok(Item::FnDef(FnDef { is_async: true, ..fn_def }))
            }
            TokenKind::Extern => self.parse_extern_block_inline(),
            _ => Err(self.error(
                format!("unexpected token `{}` at top level", self.current().text),
                vec!["expected fn, struct, enum, trait, impl, type, or extern".to_string()],
            )),
        }
    }

    fn parse_fn(&mut self, pub_: bool) -> Result<FnDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'fn'

        let is_async = if matches!(self.current().kind, TokenKind::Async) {
            self.advance(); true
        } else { false };

        let is_unsafe = if matches!(self.current().kind, TokenKind::Unsafe) {
            self.advance(); true
        } else { false };

        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(&TokenKind::RParen)?;

        let return_type = if matches!(self.current().kind, TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else { None };

        self.skip_newlines();
        let body = self.parse_block()?;
        let span = start.merge(&self.current().span);

        Ok(FnDef { name, params, return_type, body, pub_, is_async: false, is_unsafe, span })
    }

    fn parse_params(&mut self) -> Result<Vec<Param>, ParseError> {
        let mut params = Vec::new();
        while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::RParen) { break; }

            let span = self.current().span.clone();
            let mutable = if matches!(self.current().kind, TokenKind::Mut) {
                self.advance(); true
            } else { false };

            // self param
            if matches!(self.current().kind, TokenKind::Self_) {
                let s = self.advance().span.clone();
                params.push(Param {
                    name: "self".to_string(),
                    ty: TypeExpr::Named("Self".to_string()),
                    mutable,
                    span: s,
                });
            } else {
                let (name, _) = self.expect_ident()?;
                self.expect(&TokenKind::Colon)?;
                let ty = self.parse_type()?;
                params.push(Param { name, ty, mutable, span });
            }

            if matches!(self.current().kind, TokenKind::Comma) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(params)
    }

    fn parse_extern_block_inline(&mut self) -> Result<Item, ParseError> {
        // Extern types are imported via ast::* glob
        let span = self.current().span.clone();
        self.advance(); // consume 'extern'

        // link kind: static | dynamic
        let link_kind = {
            let kw = if let TokenKind::Ident(ref s) = self.current().kind { s.clone() } else { String::new() };
            match kw.as_str() {
                "static"  => { self.advance(); ExternLinkKind::Static }
                "dynamic" => { self.advance(); ExternLinkKind::Dynamic }
                _         => ExternLinkKind::Static,
            }
        };

        // language: [c] [rust] [cpp]
        let mut lang = ExternLang::C;
        let mut library = None;
        if matches!(self.current().kind, TokenKind::LBracket) {
            self.advance(); // [
            {
                let s = if let TokenKind::Ident(ref ss) = self.current().kind { ss.clone() } else { String::new() };
                lang = match s.as_str() {
                    "rust" | "Rust" => ExternLang::Rust,
                    "cpp"           => ExternLang::Cpp,
                    _               => ExternLang::C,
                };
            }
            self.advance();
            if matches!(self.current().kind, TokenKind::Comma) {
                self.advance();
                if let TokenKind::StringLit(s) = &self.current().kind.clone() {
                    library = Some(s.clone());
                    self.advance();
                }
            }
            if matches!(self.current().kind, TokenKind::RBracket) { self.advance(); }
        }

        // is ... end
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
                let mut params = Vec::new();
                let mut variadic = false;
                while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                    // Check for ... variadic
                    if matches!(self.current().kind, TokenKind::DotDot) {
                        variadic = true; self.advance(); break;
                    }
                    let (pname, _) = self.expect_ident()?;
                    self.expect(&TokenKind::Colon)?;
                    let ty = self.parse_type()?;
                    params.push(Param { name: pname, ty, mutable: false, span: fspan.clone() });
                    if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                }
                self.expect(&TokenKind::RParen)?;
                let ret = if matches!(self.current().kind, TokenKind::Arrow) {
                    self.advance(); Some(self.parse_type()?)
                } else { None };
                functions.push(ExternFnDecl { name, params, return_type: ret, variadic, span: fspan });
            }
            self.skip_newlines();
        }
        self.expect(&TokenKind::End)?;
        Ok(Item::Extern(ExternBlock { lang, link_kind, library, functions, span }))
    }

    fn parse_block(&mut self) -> Result<Vec<Stmt>, ParseError> {
        self.skip_newlines();
        let mut stmts = Vec::new();
        // H# uses 'is...end' blocks
        // But also support single-line: fn foo() -> int = expr
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance();
            self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End | TokenKind::EOF) { break; }
                match self.parse_stmt() {
                    Ok(s) => stmts.push(s),
                    Err(e) => {
                        self.errors.report(e);
                        self.recover();
                    }
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        } else if matches!(self.current().kind, TokenKind::Assign) {
            // Single expression body: fn foo() -> int = expr
            self.advance();
            let expr = self.parse_expr(0)?;
            let span = expr.span().clone();
            stmts.push(Stmt::Return(Some(expr), span));
        } else {
            return Err(self.error(
                "expected `is` to start a function body",
                vec!["write `is` before the function body and `end` after".to_string()],
            ));
        }
        Ok(stmts)
    }

    fn parse_struct(&mut self, pub_: bool) -> Result<StructDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'struct'
        let (name, _) = self.expect_ident()?;
        let generics = self.parse_generics_decl()?;
        self.skip_newlines();

        let mut fields = Vec::new();
        // struct fields: is ... end
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance();
            self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End) { break; }
                let fpub = if matches!(self.current().kind, TokenKind::Pub) {
                    self.advance(); true
                } else { false };
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
        Ok(StructDef { name, fields, generics, pub_, span })
    }

    fn parse_enum(&mut self, pub_: bool) -> Result<EnumDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'enum'
        let (name, _) = self.expect_ident()?;
        let generics = self.parse_generics_decl()?;
        self.skip_newlines();

        let mut variants = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance();
            self.skip_newlines();
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
        Ok(EnumDef { name, variants, generics, pub_, span })
    }

    fn parse_trait(&mut self, pub_: bool) -> Result<TraitDef, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'trait'
        let (name, _) = self.expect_ident()?;
        self.skip_newlines();

        let mut methods = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance();
            self.skip_newlines();
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
                        self.advance();
                        Some(self.parse_type()?)
                    } else { None };

                    self.skip_newlines();
                    let default_body = if matches!(self.current().kind, TokenKind::Is) {
                        Some(self.parse_block()?)
                    } else { None };

                    methods.push(TraitMethod {
                        name: mname, params, return_type: ret, default_body,
                        span: mspan,
                    });
                } else {
                    let e = self.error("expected `fn` in trait", vec![]);
                    self.errors.report(e);
                    self.recover();
                }
                self.skip_newlines();
            }
            self.expect(&TokenKind::End)?;
        }

        let span = start.merge(&self.current().span);
        Ok(TraitDef { name, methods, pub_, span })
    }

    fn parse_impl(&mut self) -> Result<ImplBlock, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'impl'
        let (type_name, _) = self.expect_ident()?;

        let trait_name = if matches!(self.current().kind, TokenKind::Colon) {
            self.advance();
            let (tname, _) = self.expect_ident()?;
            Some(tname)
        } else { None };

        self.skip_newlines();
        let mut methods = Vec::new();
        if matches!(self.current().kind, TokenKind::Is) {
            self.advance();
            self.skip_newlines();
            while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::End) { break; }
                let pub_ = if matches!(self.current().kind, TokenKind::Pub) {
                    self.advance(); true
                } else { false };
                if matches!(self.current().kind, TokenKind::Fn) {
                    match self.parse_fn(pub_) {
                        Ok(f) => methods.push(f),
                        Err(e) => { self.errors.report(e); self.recover(); }
                    }
                } else {
                    let e = self.error("expected `fn` in impl block", vec![]);
                    self.errors.report(e);
                    self.recover();
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
        self.advance(); // 'type'
        let (name, _) = self.expect_ident()?;
        self.expect(&TokenKind::Assign)?;
        let ty = self.parse_type()?;
        let span = start.merge(&self.current().span);
        Ok(Item::TypeAlias { name, ty, pub_, span })
    }

    fn parse_generics_decl(&mut self) -> Result<Vec<String>, ParseError> {
        let mut generics = Vec::new();
        if matches!(self.current().kind, TokenKind::Lt) {
            self.advance();
            while !matches!(self.current().kind, TokenKind::Gt | TokenKind::EOF) {
                let (g, _) = self.expect_ident()?;
                generics.push(g);
                if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
            }
            self.expect(&TokenKind::Gt)?;
        }
        Ok(generics)
    }

    // ── Types ─────────────────────────────────────────────────────────────────

    fn parse_type(&mut self) -> Result<TypeExpr, ParseError> {
        let mut ty = self.parse_type_base()?;
        // Optional type: T?
        if matches!(self.current().kind, TokenKind::Question) {
            self.advance();
            ty = TypeExpr::Optional(Box::new(ty));
        }
        Ok(ty)
    }

    fn parse_type_base(&mut self) -> Result<TypeExpr, ParseError> {
        match &self.current().kind {
            TokenKind::TInt   => { self.advance(); Ok(TypeExpr::Named("int".into())) }
            TokenKind::TUint  => { self.advance(); Ok(TypeExpr::Named("uint".into())) }
            TokenKind::TI8    => { self.advance(); Ok(TypeExpr::Named("i8".into())) }
            TokenKind::TI16   => { self.advance(); Ok(TypeExpr::Named("i16".into())) }
            TokenKind::TI32   => { self.advance(); Ok(TypeExpr::Named("i32".into())) }
            TokenKind::TI64   => { self.advance(); Ok(TypeExpr::Named("i64".into())) }
            TokenKind::TI128  => { self.advance(); Ok(TypeExpr::Named("i128".into())) }
            TokenKind::TU8    => { self.advance(); Ok(TypeExpr::Named("u8".into())) }
            TokenKind::TU16   => { self.advance(); Ok(TypeExpr::Named("u16".into())) }
            TokenKind::TU32   => { self.advance(); Ok(TypeExpr::Named("u32".into())) }
            TokenKind::TU64   => { self.advance(); Ok(TypeExpr::Named("u64".into())) }
            TokenKind::TU128  => { self.advance(); Ok(TypeExpr::Named("u128".into())) }
            TokenKind::TF32   => { self.advance(); Ok(TypeExpr::Named("f32".into())) }
            TokenKind::TF64   => { self.advance(); Ok(TypeExpr::Named("f64".into())) }
            TokenKind::TBool  => { self.advance(); Ok(TypeExpr::Named("bool".into())) }
            TokenKind::TString => { self.advance(); Ok(TypeExpr::Named("string".into())) }
            TokenKind::TBytes => { self.advance(); Ok(TypeExpr::Named("bytes".into())) }
            TokenKind::TVoid  => { self.advance(); Ok(TypeExpr::Void) }
            TokenKind::TAny   => { self.advance(); Ok(TypeExpr::Named("any".into())) }
            TokenKind::BitAnd => {
                self.advance();
                let mutable = if matches!(self.current().kind, TokenKind::Mut) {
                    self.advance(); true
                } else { false };
                let inner = self.parse_type()?;
                if mutable { Ok(TypeExpr::RefMut(Box::new(inner))) }
                else { Ok(TypeExpr::Ref(Box::new(inner))) }
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
                let name = name.clone();
                self.advance();
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

    pub fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        self.skip_newlines();
        match &self.current().kind {
            TokenKind::Let => self.parse_let(),
            TokenKind::Return => {
                let span = self.current().span.clone();
                self.advance();
                let expr = if !matches!(self.current().kind, TokenKind::Newline | TokenKind::EOF | TokenKind::End) {
                    Some(self.parse_expr(0)?)
                } else { None };
                Ok(Stmt::Return(expr, span))
            }
            TokenKind::Use => {
                let (kind, alias, span) = self.parse_import()?;
                Ok(Stmt::Import(kind, alias, span))
            }
            TokenKind::Break => {
                let span = self.current().span.clone();
                self.advance();
                Ok(Stmt::Break(None, span))
            }
            TokenKind::Continue => {
                let span = self.current().span.clone();
                self.advance();
                Ok(Stmt::Continue(span))
            }
            TokenKind::Fn | TokenKind::Struct | TokenKind::Enum |
            TokenKind::Trait | TokenKind::Impl | TokenKind::Type | TokenKind::Pub => {
                let item = self.parse_item()?;
                Ok(Stmt::Item(item))
            }
            _ => {
                let expr = self.parse_expr(0)?;
                let span = expr.span().clone();
                Ok(Stmt::Expr(expr, span))
            }
        }
    }

    fn parse_let(&mut self) -> Result<Stmt, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'let'
        let mutable = if matches!(self.current().kind, TokenKind::Mut) {
            self.advance(); true
        } else { false };

        let (name, _) = self.expect_ident()?;

        let ty = if matches!(self.current().kind, TokenKind::Colon) {
            self.advance();
            Some(self.parse_type()?)
        } else { None };

        let value = if matches!(self.current().kind, TokenKind::Assign) {
            self.advance();
            Some(self.parse_expr(0)?)
        } else { None };

        let span = start.merge(&self.current().span);
        Ok(Stmt::Let { name, ty, mutable, value, span })
    }

    // ── Expressions (Pratt parser) ─────────────────────────────────────────────

    fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_prefix()?;

        loop {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::EOF | TokenKind::End |
                TokenKind::Newline | TokenKind::Comma | TokenKind::RParen |
                TokenKind::RBracket | TokenKind::RBrace | TokenKind::Semicolon) {
                break;
            }

            let (l_bp, r_bp) = if let Some(bp) = infix_bp(&self.current().kind) {
                bp
            } else {
                break;
            };

            if l_bp < min_bp { break; }

            let op_tok = self.advance().clone();
            let span = lhs.span().merge(&op_tok.span);

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

            // Method call: expr.method(args)
            if matches!(op_tok.kind, TokenKind::Dot) {
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

            // Index
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

            // As cast
            if matches!(op_tok.kind, TokenKind::As) {
                let ty = self.parse_type()?;
                let s = span.clone();
                lhs = Expr::Cast(Box::new(lhs), ty, s);
                continue;
            }

            // Error propagation: expr?
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

    fn parse_closure_expr(&mut self) -> Result<Expr, ParseError> {
        let span = self.current().span.clone();
        self.advance(); // consume first |

        // Parse params as regular Params (reuse existing type)
        let mut params = Vec::new();
        while !matches!(self.current().kind, TokenKind::Pipe | TokenKind::EOF) {
            let p_span = self.current().span.clone();
            let mutable = if matches!(self.current().kind, TokenKind::Mut) {
                self.advance(); true
            } else { false };
            let (name, _) = self.expect_ident()?;
            let ty = if matches!(self.current().kind, TokenKind::Colon) {
                self.advance();
                self.parse_type()?
            } else { TypeExpr::Named("int".into()) }; // default type
            params.push(Param { name, ty, mutable, span: p_span });
            if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
        }
        if matches!(self.current().kind, TokenKind::Pipe) { self.advance(); } // closing |

        // Optional return type: -> T
        let return_type = if matches!(self.current().kind, TokenKind::Arrow) {
            self.advance();
            Some(self.parse_type()?)
        } else { None };

        // Body: `is ... end` block OR single expression
        // parse_block() handles `is ... end` internally
        let body = if matches!(self.current().kind, TokenKind::Is) {
            self.parse_block()?
        } else {
            // Single-expression body: |x| x + 1
            let e = self.parse_expr(0)?;
            let s = e.span().clone();
            vec![Stmt::Return(Some(e), s)]
        };

        let end_sp = self.current().span.clone();
        Ok(Expr::Closure { params, return_type, body, span: span.merge(&end_sp) })
    }

    fn parse_prefix(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        // await expr
        if matches!(self.current().kind, TokenKind::Await) {
            let span = self.current().span.clone();
            self.advance();
            let inner = self.parse_expr(0)?;
            let s = span.merge(inner.span());
            return Ok(Expr::Await(Box::new(inner), s));
        }

        // Closure: |params| body
        if matches!(self.current().kind, TokenKind::Pipe) {
            return self.parse_closure_expr();
        }
        match &self.current().kind.clone() {
            TokenKind::Integer(v) => {
                let v = *v;
                let span = self.current().span.clone();
                self.advance();
                Ok(Expr::Literal(Literal::Int(v), span))
            }
            TokenKind::Float(v) => {
                let v = *v;
                let span = self.current().span.clone();
                self.advance();
                Ok(Expr::Literal(Literal::Float(v), span))
            }
            TokenKind::StringLit(s) => {
                let s = s.clone();
                let span = self.current().span.clone();
                self.advance();
                Ok(Expr::Literal(Literal::String(s), span))
            }
            TokenKind::Bool(b) => {
                let b = *b;
                let span = self.current().span.clone();
                self.advance();
                Ok(Expr::Literal(Literal::Bool(b), span))
            }
            TokenKind::Nil => {
                let span = self.current().span.clone();
                self.advance();
                Ok(Expr::Literal(Literal::Nil, span))
            }
            TokenKind::Self_ => {
                let span = self.current().span.clone();
                self.advance();
                Ok(Expr::SelfExpr(span))
            }
            // Keywords that can also be used as function call names
            TokenKind::Write | TokenKind::Manual | TokenKind::Arena => {
                // Treat as identifier — allows write(...), arena(...), etc.
                let name = match &self.current().kind {
                    TokenKind::Write  => "write".to_string(),
                    TokenKind::Manual => "manual".to_string(),
                    TokenKind::Arena  => "arena".to_string(),
                    _ => unreachable!(),
                };
                let span = self.current().span.clone();
                self.advance();
                // If followed by ( it's a function call
                if matches!(self.current().kind, TokenKind::LParen) {
                    self.advance(); // consume (
                    let mut args = Vec::new();
                    while !matches!(self.current().kind, TokenKind::RParen | TokenKind::EOF) {
                        args.push(self.parse_expr(0)?);
                        if matches!(self.current().kind, TokenKind::Comma) { self.advance(); }
                    }
                    if matches!(self.current().kind, TokenKind::RParen) { self.advance(); }
                    let s = span.merge(&self.current().span);
                    Ok(Expr::Call(Box::new(Expr::Ident(name, span.clone())), args, s))
                } else {
                    Ok(Expr::Ident(name, span))
                }
            }
            TokenKind::Ident(_) => self.parse_ident_expr(),
            TokenKind::Minus => {
                self.advance();
                let expr = self.parse_prefix()?;
                let s = start.merge(expr.span());
                Ok(Expr::UnOp(UnOp::Neg, Box::new(expr), s))
            }
            TokenKind::Not => {
                self.advance();
                let expr = self.parse_prefix()?;
                let s = start.merge(expr.span());
                Ok(Expr::UnOp(UnOp::Not, Box::new(expr), s))
            }
            TokenKind::BitNot => {
                self.advance();
                let expr = self.parse_prefix()?;
                let s = start.merge(expr.span());
                Ok(Expr::UnOp(UnOp::BitNot, Box::new(expr), s))
            }
            TokenKind::BitAnd => {
                self.advance();
                let mutable = if matches!(self.current().kind, TokenKind::Mut) {
                    self.advance(); true
                } else { false };
                let expr = self.parse_prefix()?;
                let s = start.merge(expr.span());
                if mutable {
                    Ok(Expr::UnOp(UnOp::RefMut, Box::new(expr), s))
                } else {
                    Ok(Expr::UnOp(UnOp::Ref, Box::new(expr), s))
                }
            }
            TokenKind::Star => {
                self.advance();
                let expr = self.parse_prefix()?;
                let s = start.merge(expr.span());
                Ok(Expr::UnOp(UnOp::Deref, Box::new(expr), s))
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
            TokenKind::If => self.parse_if(),
            TokenKind::Match => self.parse_match(),
            TokenKind::While => self.parse_while(),
            TokenKind::For => self.parse_for(),
            TokenKind::Is => {
                let body = self.parse_block()?;
                let s = start.merge(&self.current().span);
                Ok(Expr::Do { body, span: s })
            }
            TokenKind::Unsafe => {
                self.advance();
                let arena = if matches!(self.current().kind, TokenKind::Arena) {
                    self.advance();
                    let size = if matches!(self.current().kind, TokenKind::LParen) {
                        self.advance();
                        if let TokenKind::Integer(n) = &self.current().kind.clone() {
                            let n = *n as usize;
                            self.advance();
                            self.expect(&TokenKind::RParen)?;
                            Some(n)
                        } else {
                            self.expect(&TokenKind::RParen)?;
                            None
                        }
                    } else { None };
                    Some(ArenaConfig { size, mode: crate::ast::UnsafeMode::Arena(size) })
                } else { None };
                let body = self.parse_block()?;
                let s = start.merge(&self.current().span);
                Ok(Expr::Unsafe(body, arena, s))
            }
            TokenKind::Return => {
                self.advance();
                let val = if !matches!(self.current().kind,
                    TokenKind::Newline | TokenKind::EOF | TokenKind::End |
                    TokenKind::Comma | TokenKind::RParen) {
                    Some(Box::new(self.parse_expr(0)?))
                } else { None };
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

    fn parse_if(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'if'
        let condition = self.parse_expr(0)?;
        self.skip_newlines();
        if matches!(self.current().kind, TokenKind::Then) { self.advance(); }
        self.skip_newlines();
        let then_body = self.parse_block()?;

        let mut elsif_branches = Vec::new();
        let mut else_body = None;

        self.skip_newlines();
        loop {
            if matches!(self.current().kind, TokenKind::Elsif) {
                self.advance();
                let cond = self.parse_expr(0)?;
                self.skip_newlines();
                if matches!(self.current().kind, TokenKind::Then) { self.advance(); }
                let body = self.parse_block()?;
                elsif_branches.push((cond, body));
                self.skip_newlines();
            } else if matches!(self.current().kind, TokenKind::Else) {
                self.advance();
                self.skip_newlines();
                let body = self.parse_block()?;
                else_body = Some(body);
                break;
            } else {
                break;
            }
        }

        let s = start.merge(&self.current().span);
        Ok(Expr::If { condition: Box::new(condition), then_body, elsif_branches, else_body, span: s })
    }

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        self.advance(); // 'match'
        let subject = self.parse_expr(0)?;
        self.skip_newlines();
        self.expect(&TokenKind::Is)?;
        self.skip_newlines();

        let mut arms = Vec::new();
        while !matches!(self.current().kind, TokenKind::End | TokenKind::EOF) {
            self.skip_newlines();
            if matches!(self.current().kind, TokenKind::End) { break; }
            let arm_span = self.current().span.clone();
            let pattern = self.parse_pattern()?;
            let guard = if matches!(self.current().kind, TokenKind::If) {
                self.advance();
                Some(self.parse_expr(0)?)
            } else { None };
            self.expect(&TokenKind::FatArrow)?;
            let body = if matches!(self.current().kind, TokenKind::Is) {
                self.parse_block()?
            } else {
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

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        let start = self.current().span.clone();
        match &self.current().kind.clone() {
            TokenKind::Ident(name) if name == "_" => {
                self.advance();
                Ok(Pattern::Wildcard(start))
            }
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.advance();
                if matches!(self.current().kind, TokenKind::LParen) {
                    self.advance();
                    let inner = self.parse_pattern()?;
                    self.expect(&TokenKind::RParen)?;
                    let s = start.merge(&self.current().span);
                    Ok(Pattern::Enum { variant: name, inner: Some(Box::new(inner)), span: s })
                } else {
                    Ok(Pattern::Ident(name, start))
                }
            }
            TokenKind::Integer(v) => {
                let v = *v;
                self.advance();
                Ok(Pattern::Literal(Literal::Int(v), start))
            }
            TokenKind::StringLit(s) => {
                let s = s.clone();
                self.advance();
                Ok(Pattern::Literal(Literal::String(s), start))
            }
            TokenKind::Bool(b) => {
                let b = *b;
                self.advance();
                Ok(Pattern::Literal(Literal::Bool(b), start))
            }
            TokenKind::Nil => {
                self.advance();
                Ok(Pattern::Literal(Literal::Nil, start))
            }
            _ => Err(self.error(
                format!("expected pattern, found `{}`", self.current().text),
                vec!["valid patterns: variable name, literal, or _".to_string()],
            )),
        }
    }

    fn parse_while(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        self.advance();
        let condition = self.parse_expr(0)?;
        self.skip_newlines();
        let body = self.parse_block()?;
        let s = start.merge(&self.current().span);
        Ok(Expr::While { condition: Box::new(condition), body, span: s })
    }

    fn parse_for(&mut self) -> Result<Expr, ParseError> {
        let start = self.current().span.clone();
        self.advance();
        let pattern = self.parse_pattern()?;
        self.expect(&TokenKind::In)?;
        let iterable = self.parse_expr(0)?;
        self.skip_newlines();
        let body = self.parse_block()?;
        let s = start.merge(&self.current().span);
        Ok(Expr::For { pattern, iterable: Box::new(iterable), body, span: s })
    }
}

// ── Pratt parser helpers ───────────────────────────────────────────────────────

fn infix_bp(kind: &TokenKind) -> Option<(u8, u8)> {
    match kind {
        TokenKind::Question => Some((100, 101)),  // ? operator — high postfix precedence
        TokenKind::Assign | TokenKind::PlusAssign | TokenKind::MinusAssign |
        TokenKind::StarAssign | TokenKind::SlashAssign => Some((2, 1)),
        TokenKind::Or => Some((4, 5)),
        TokenKind::And => Some((6, 7)),
        // TokenKind::Pipe (single |) is used only for closures, not as binary operator
        // Use bitor() builtin for bitwise OR
        TokenKind::BitXor => Some((10, 11)),
        TokenKind::BitAnd => Some((12, 13)),
        TokenKind::Eq | TokenKind::NotEq => Some((14, 15)),
        TokenKind::Lt | TokenKind::Gt | TokenKind::LtEq | TokenKind::GtEq => Some((16, 17)),
        TokenKind::Shl | TokenKind::Shr => Some((18, 19)),
        TokenKind::Plus | TokenKind::Minus => Some((20, 21)),
        TokenKind::Star | TokenKind::Slash | TokenKind::Percent => Some((22, 23)),
        TokenKind::As => Some((24, 25)),
        TokenKind::Dot => Some((30, 31)),
        TokenKind::LBracket => Some((30, 31)),
        TokenKind::DotDot | TokenKind::DotDotEq => Some((18, 19)),
        _ => None,
    }
}

fn token_to_binop(kind: &TokenKind) -> Option<BinOp> {
    match kind {
        TokenKind::Plus => Some(BinOp::Add),
        TokenKind::Minus => Some(BinOp::Sub),
        TokenKind::Star => Some(BinOp::Mul),
        TokenKind::Slash => Some(BinOp::Div),
        TokenKind::Percent => Some(BinOp::Mod),
        TokenKind::Eq => Some(BinOp::Eq),
        TokenKind::NotEq => Some(BinOp::NotEq),
        TokenKind::Lt => Some(BinOp::Lt),
        TokenKind::Gt => Some(BinOp::Gt),
        TokenKind::LtEq => Some(BinOp::LtEq),
        TokenKind::GtEq => Some(BinOp::GtEq),
        TokenKind::And => Some(BinOp::And),
        TokenKind::Or => Some(BinOp::Or),
        TokenKind::BitAnd => Some(BinOp::BitAnd),
        // Pipe no longer maps to BitOr (use bitor() builtin)
        TokenKind::BitXor => Some(BinOp::BitXor),
        TokenKind::Shl => Some(BinOp::Shl),
        TokenKind::Shr => Some(BinOp::Shr),
        _ => None,
    }
}

fn compound_op(kind: &TokenKind) -> Option<BinOp> {
    match kind {
        TokenKind::PlusAssign => Some(BinOp::Add),
        TokenKind::MinusAssign => Some(BinOp::Sub),
        TokenKind::StarAssign => Some(BinOp::Mul),
        TokenKind::SlashAssign => Some(BinOp::Div),
        _ => None,
    }
}

fn token_kind_name(kind: &TokenKind) -> &'static str {
    match kind {
        TokenKind::LParen => "(",
        TokenKind::RParen => ")",
        TokenKind::LBrace => "{",
        TokenKind::RBrace => "}",
        TokenKind::LBracket => "[",
        TokenKind::RBracket => "]",
        TokenKind::Colon => ":",
        TokenKind::ColonColon => "::",
        TokenKind::Comma => ",",
        TokenKind::Arrow => "->",
        TokenKind::FatArrow => "=>",
        TokenKind::Assign => "=",
        TokenKind::Is => "is",
        TokenKind::End => "end",
        TokenKind::In => "in",
        _ => "token",
    }
}

/// Parse new H# use path syntax:
/// "std -> io -> keyboard"        → Std { path: ["io","keyboard"], alias }
/// "vira -> scanner/1.2"          → Vira { name:"scanner", version:"1.2", alias }
/// "python -> numpy"              → Python { name:"numpy", version:None, alias }
/// "python -> numpy/1.26"         → Python { name:"numpy", version:"1.26", alias }
/// "github.com/user/repo"         → GitRepo { url, alias }
/// "gitlab.com/user/repo"         → GitRepo { url, alias }
/// "file -> path/lib.h#"          → File { path, alias }
/// "lib:static -> file.a"         → LibStatic { path, alias }
/// "lib:dynamic -> file.so"       → LibDynamic { path, alias }
fn parse_use_path(path: &str, alias: Option<String>) -> Option<ImportKind> {
    // Split on " -> " (with spaces)
    let arrow = " -> ";

    // Bytes repository: "bytes -> pkgname" or "bytes -> pkgname/1.2"
    if path.starts_with("bytes") && path.contains(arrow) {
        let rest = path.splitn(2, arrow).nth(1)?.trim();
        let (name, ver) = if let Some(idx) = rest.rfind('/') {
            let n = &rest[..idx]; let v = &rest[idx+1..];
            if v.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                (n.to_string(), Some(v.to_string()))
            } else { (rest.to_string(), None) }
        } else { (rest.to_string(), None) };
        return Some(ImportKind::BytesRepo { name, version: ver, alias });
    }

    // Python interop: "python -> numpy" or "python -> numpy/1.26"
    if path.starts_with("python") && path.contains(arrow) {
        let rest = path.splitn(2, arrow).nth(1)?.trim();
        let (name, ver) = if let Some(idx) = rest.rfind('/') {
            let n = &rest[..idx]; let v = &rest[idx+1..];
            if v.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                (n.to_string(), Some(v.to_string()))
            } else { (rest.to_string(), None) }
        } else { (rest.to_string(), None) };
        return Some(ImportKind::Python { name, version: ver, alias });
    }

    if path.starts_with("std") && path.contains(arrow) {
        let parts: Vec<String> = path.split(arrow)
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty() && s != "std")
            .collect();
        if !parts.is_empty() {
            return Some(ImportKind::Std { path: parts, alias });
        }
    }
    if path.starts_with("vira") && path.contains(arrow) {
        let rest = path.splitn(2, arrow).nth(1)?.trim();
        let (name, ver) = if let Some(idx) = rest.rfind('/') {
            let n = &rest[..idx];
            let v = &rest[idx+1..];
            if v.chars().next().map(|c| c.is_ascii_digit()).unwrap_or(false) {
                (n.to_string(), Some(v.to_string()))
            } else { (rest.to_string(), None) }
        } else { (rest.to_string(), None) };
        return Some(ImportKind::Vira { name, version: ver, alias });
    }
    if path.starts_with("file") && path.contains(arrow) {
        let p = path.splitn(2, arrow).nth(1)?.trim().to_string();
        return Some(ImportKind::File { path: p, alias });
    }
    if path.starts_with("lib:static") && path.contains(arrow) {
        let p = path.splitn(2, arrow).nth(1)?.trim().to_string();
        return Some(ImportKind::LibStatic { path: p, alias });
    }
    if path.starts_with("lib:dynamic") && path.contains(arrow) {
        let p = path.splitn(2, arrow).nth(1)?.trim().to_string();
        return Some(ImportKind::LibDynamic { path: p, alias });
    }
    // Go-style git repo: github.com/user/repo or gitlab.com/user/repo
    if path.starts_with("github.com/") || path.starts_with("gitlab.com/") || path.starts_with("git.sr.ht/") {
        return Some(ImportKind::GitRepo { url: path.to_string(), alias });
    }
    // Backward-compat with old std: syntax
    if let Some(rest) = path.strip_prefix("std:") {
        let parts: Vec<String> = rest.split("::").map(|s| s.to_string()).collect();
        return Some(ImportKind::Std { path: parts, alias });
    }
    None
}
