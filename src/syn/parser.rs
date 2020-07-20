#[cfg(test)]
mod test;

use super::*;
use super::lex::S;
use crate::syn::lex::FloatLiteral;

#[derive(Debug)]
pub enum PError {
    Io(io::Error),
    Lex,
    Parse,
}

pub type PResult<T> = Result<T, PError>;

pub trait Fs {
    fn read_file(&mut self, path: &Path) -> io::Result<String>;
}

pub struct Parser<'a> {
    s: &'a str,
    lex: Lexer<'a>,
    buf: [S<Token>; 4],
    buf_pos: usize,
    buf_len: usize,
    ast: &'a mut Ast,
    mod_name: Option<&'a Ident>,
    path: PathBuf,
    fs: &'a mut dyn Fs,
}

impl<'a> Parser<'a> {
    fn new(
        s: &'a str,
        mod_name: Option<&'a Ident>,
        path: PathBuf,
        fs: &'a mut dyn Fs,
        ast: &'a mut Ast,
    ) -> Self {
        Self {
            s,
            lex: Lexer::new(s),
            buf: [S::new(Span::new(0, 0), Token::Eof); 4],
            buf_pos: 0,
            buf_len: 0,
            ast,
            mod_name,
            path,
            fs,
        }
    }

    fn read_file(fs: &mut dyn Fs, path: &Path) -> PResult<String> {
        fs.read_file(path).map_err(PError::Io)
    }

    fn parse(mut self) -> PResult<()> {
        let root = self.module_decl_inner(None)?;
        self.ast.root = root;
        if self.lex.is_ok() {
            Ok(())
        } else {
            Err(PError::Lex)
        }
    }

    fn maybe_vis(&mut self) -> Option<S<Vis>> {
        let publ = self.maybe(Token::Keyword(Keyword::Pub))?.map(|_| {});
        let restrict = if self.maybe(Token::BlockOpen(lex::Block::Paren)).is_some() {
            unimplemented!();
        } else {
            None
        };
        Some(publ.span.spanned(Vis {
            restrict,
        }))
    }

    fn maybe_decl_item(&mut self) -> PResult<Option<S<NodeId>>> {
        let vis = self.maybe_vis();
        let tok0 = self.nth(0);
        Ok(Some(match tok0.value {
            Token::Keyword(Keyword::Unsafe) => {
                let tok1 = self.nth(1);
                match tok1.value {
                    Token::Keyword(Keyword::Fn) => self.fn_decl(vis)?,
                    Token::Keyword(Keyword::Static) => unimplemented!(),
                    _ => {
                        return self.fatal(tok1.span,
                            &format!("expected `fn` or `static`, found `{:?}`", tok1.value));
                    }
                }
            }
            Token::Keyword(Keyword::Fn) => self.fn_decl(vis)?,
            Token::Keyword(Keyword::Mod) => self.module_decl(vis)?,
            Token::Keyword(Keyword::Static) => unimplemented!(),
            Token::Keyword(Keyword::Use) => self.use_stmt(vis)?,
            _ => {
                if let Some(vis) = vis {
                    return self.fatal(vis.span,
                        &format!("expected `<decl_item>` after visibility modifier, found `{:?}`", tok0.value));
                }
                return Ok(None);
            }
        }))
    }

    fn module_decl_inner(&mut self, name: Option<ModuleName>) -> PResult<S<NodeId>> {
        let mut items = Vec::new();
        loop {
            if let Some(item) = self.maybe_decl_item()? {
                items.push(item);
            } else {
                let tok = self.nth(0);
                if tok.value != Token::Eof {
                    return self.fatal(tok.span,
                        &format!("expected `extern`, `fn` or `static`, found `{:?}`", tok.value));
                }
                break;
            }
        }
        let span_start = items.first().map(|v| v.span.start).unwrap_or(0);
        let span_end = items.last().map(|v| v.span.end).unwrap_or(0);
        Ok(Span::new(span_start, span_end).spanned(self.ast.insert_module_decl(ModuleDecl {
            name,
            items,
        })))
    }

    // [pub] mod foo { ... }
    // [pub] mod foo;
    fn module_decl(&mut self, vis: Option<S<Vis>>) -> PResult<S<NodeId>> {
        let modu = self.expect(Token::Keyword(Keyword::Mod))?;
        let name = self.ident()?;
        let name = ModuleName {
            name,
            vis,
        };
        let mut r = if let Token::BlockOpen(lex::Block::Brace) = self.nth(0).value {
            self.consume();
            let r = self.module_decl_inner(Some(name))?;
            self.expect(Token::BlockClose(lex::Block::Brace))?;
            r
        } else {
            self.expect(Token::Semi)?;

            let mut path = self.path.clone();
            if let Some(mod_name) = &self.mod_name {
                path.push(mod_name);
            }
            path.push(format!("{}.tsar", name.name.value));
            let s = Self::read_file(self.fs, &path)?;
            Parser::new(&s, Some(&name.name.value), path, self.fs, &mut self.ast).parse()?;
            let r = std::mem::replace(&mut self.ast.root,
                Span::new(0, 0).spanned(NodeId::null()));
            assert_ne!(r.value, NodeId::null());
            r
        };
        r.span.start = modu.span.start;
        Ok(r)
    }

    // use <path>;
    fn use_stmt(&mut self, vis: Option<S<Vis>>) -> PResult<S<NodeId>> {
        let span_start = self.expect(Token::Keyword(Keyword::Use))?.span.start;
        let anchor = self.maybe_path_anchor()?;
        let path = self.use_path()?.value;
        let span_end = self.expect(Token::Semi)?.span.end;
        Ok(Span::new(span_start, span_end).spanned(self.ast.insert_use_stmt(UseStmt {
            vis,
            path: Span::new(span_start, span_end).spanned(AnchoredPath {
                anchor: anchor.map(|v| v.value),
                path,
            }),
        })))
    }

    #[inline(always)]
    fn buf_pos(&self, offset: usize) -> usize {
        (self.buf_pos + offset) % self.buf.len()
    }

    fn fill_buf(&mut self) {
        while self.buf_len < self.buf.len() {
            self.buf[self.buf_pos(self.buf_len)] = self.lex.next();
            self.buf_len += 1;
        }
    }

    fn nth(&mut self, i: usize) -> S<Token> {
        assert!(i < self.buf.len());
        self.fill_buf();
        self.buf[self.buf_pos(i)]
    }

    #[must_use]
    fn next(&mut self) -> S<Token> {
        let r = self.nth(0);
        self.buf_pos = self.buf_pos(1);
        self.buf_len -= 1;
        r
    }

    fn prepend_buf(&mut self, tok: S<Token>) {
        assert!(self.buf_len < self.buf.len());
        if self.buf_pos == 0 {
            self.buf_pos = self.buf_len - 1;
        } else {
            self.buf_pos -= 1;
        }
        self.buf[self.buf_pos] = tok;
        self.buf_len += 1;
    }

    fn fatal<T>(&self, span: Span, msg: &str) -> PResult<T> {
        panic!("[{:?}] {}", span.range(), msg);
        eprintln!("[{:?}] {}", span.range(), msg);
        Err(PError::Parse)
    }

    fn fn_decl(&mut self, vis: Option<S<Vis>>) -> PResult<S<NodeId>> {
        let unsaf = self.maybe(Token::Keyword(Keyword::Unsafe))
            .map(|v| v.map(|_| {}));

        let tok = self.expect(Token::Keyword(Keyword::Fn))?;
        let span_start = vis.as_ref().map(|v| v.span.start)
            .or(unsaf.as_ref().map(|v| v.span.start))
            .unwrap_or(tok.span.start);

        let name = self.ident()?;
        let ty_args = self.maybe_formal_ty_args()?;

        let mut args = Vec::new();
        self.expect(Token::BlockOpen(lex::Block::Paren))?;
        let mut delimited = true;
        let mut variadic = None;
        while self.nth(0).value != Token::BlockClose(lex::Block::Paren) {
            if !delimited {
                let tok = self.nth(0);
                return self.fatal(tok.span, &format!("expected `,` but found `{:?}`", tok.value));
            }
            if variadic.is_some() {
                self.expect(Token::BlockClose(lex::Block::Paren))?;
                break;
            }

            if self.nth(0).value == Token::DotDotDot {
                let tok = self.next();
                variadic = Some(tok.map(|_| {}));
            } else {
                let arg_name = self.ident()?;
                self.expect(Token::Colon)?;
                let arg_ty = self.ty_expr()?;
                args.push(FnDeclArg { name: arg_name, ty: arg_ty });
            }

            delimited = self.maybe(Token::Comma).is_some();
        }
        assert_eq!(self.next().value, Token::BlockClose(lex::Block::Paren));

        let ret_ty = if self.maybe(Token::RArrow).is_some() {
            Some(self.ty_expr()?)
        } else {
            None
        };

        let body = self.maybe_block()?;
        let span_end = if let Some(body) = &body {
            body.span.end
        } else {
            self.expect(Token::Semi)?.span.end
        };

        Ok(Span::new(span_start, span_end).spanned(self.ast.insert_fn_decl(FnDecl {
            name,
            vis,
            ty_args,
            args,
            ret_ty,
            unsaf,
            variadic,
            body,
        })))
    }

    fn consume(&mut self) {
        let _ = self.next();
    }

    fn expect(&mut self, tok: Token) -> PResult<S<Token>> {
        let actual = self.next();
        if actual.value == tok {
            Ok(actual)
        } else {
            self.fatal(actual.span, &format!("expected {:?} but found {:?}", tok, actual.value))
        }
    }

    fn maybe(&mut self, tok: Token) -> Option<S<Token>> {
        if self.nth(0).value == tok {
            Some(self.next())
        } else {
            None
        }
    }

    fn ident(&mut self) -> PResult<S<Ident>> {
        let tok = self.expect(Token::Ident)?;
        self.make_ident(tok.span)
    }

    fn maybe_ident(&mut self) -> PResult<Option<S<Ident>>> {
        Ok(if let Some(tok) = self.maybe(Token::Ident) {
            Some(self.make_ident(tok.span)?)
        } else {
            None
        })
    }

    fn make_ident(&self, span: Span) -> PResult<S<Ident>> {
        let s = &self.s[span.range()];
        let value = lex::ident(s);
        if value.is_empty() {
            self.fatal(span, "missing raw identifier or raw string")
        } else {
            Ok(span.spanned(value))
        }
    }

    // foo<T>
    // foo<T>::bar<U>
    // foo<T>::bar<U>::baz<V>
    fn ty_expr(&mut self) -> PResult<S<NodeId>> {
        let muta = self.maybe(Token::Keyword(Keyword::Mut))
            .map(|tok| tok.map(|_| {}));
        let tok = self.nth(0);
        let span_start = muta.map(|s| s.span.start)
            .unwrap_or(tok.span.start);

        let (span_end, data) = match tok.value {
            Token::Amp | Token::AmpAmp => {
                self.consume();
                let ty = self.ty_expr()?;
                let span_end = ty.span.end;
                let data = if tok.value == Token::AmpAmp {
                    TyData::Ref(self.ast.insert_ty_expr(TyExpr {
                        muta: None,
                        data: S::new(Span::new(tok.span.start + 1, ty.span.end),
                            TyData::Ref(ty.value)),
                    }))
                } else {
                    TyData::Ref(ty.value)
                };
                (span_end, data)
            }
            Token::Star => {
                self.consume();
                let ty = self.ty_expr()?;
                (ty.span.end, TyData::Ptr(ty.value))
            },
            Token::BlockOpen(lex::Block::Bracket) => {
                self.consume();
                let ty = self.ty_expr()?;
                let data = if self.maybe(Token::Semi).is_some() {
                    let len = self.expr(0)?;
                    TyData::Array(Array {
                        ty,
                        len,
                    })
                } else {
                    // [<ty>*]
                    let resizable = self.maybe(Token::Star).is_some();
                    TyData::Slice(Slice {
                        ty: ty.value,
                        resizable,
                    })
                };
                let span_end = self.expect(Token::BlockClose(lex::Block::Bracket))?.span.end;
                (span_end, data)
            }
            _ => {
                let path = self.sym_path(true)?;
                (path.span.end, TyData::SymPath(path.value))
            }
        };
        let data = S::new(Span::new(tok.span.start, span_end), data);
        Ok(Span::new(span_start, span_end)
            .spanned(self.ast.insert_ty_expr(TyExpr { muta, data })))
    }

    fn maybe_path_anchor(&mut self) -> PResult<Option<S<PathAnchor>>> {
        let tok = self.nth(0);

        let mut span_end = tok.span.end;
        let r = if tok.value == Token::Keyword(Keyword::Super) {
            let mut count = 1;
            loop {
                self.consume();

                if self.nth(0).value != Token::ColonColon {
                    break;
                }

                let tok = self.nth(1);
                if tok.value != Token::Keyword(Keyword::Super) {
                    break;
                }
                self.consume();
                span_end = tok.span.end;
                count += 1;
            }
            Span::new(tok.span.start, span_end).spanned(PathAnchor::Super { count })
        } else {
            tok.with_value(match tok.value {
                Token::ColonColon => {
                    self.consume();
                    PathAnchor::Root
                }
                Token::Keyword(Keyword::Package) => {
                    self.consume();
                    PathAnchor::Package
                }
                _ => return Ok(None),
            })
        };
        if r.value != PathAnchor::Root {
            self.expect(Token::ColonColon)?;
        }
        Ok(Some(r))
    }

    fn sym_path(&mut self, in_type_pos: bool) -> PResult<S<NodeId>> {
        #[derive(Clone, Copy, Debug)]
        enum State {
            Done,
            IdentOrTyArgs,
            SepOrEnd,
        }

        let anchor = self.maybe_path_anchor()?;

        let mut state = State::IdentOrTyArgs;

        let mut items = Vec::new();
        let mut ident = None;
        let mut ty_args = Vec::new();

        loop {
            state = match state {
                State::IdentOrTyArgs => {
                    if let Some(next_ident) = self.maybe_ident()? {
                        if let Some(ident) = std::mem::replace(&mut ident, Some(next_ident)) {
                            let ty_args = if in_type_pos {
                                self.maybe_path_ty_args()?
                            } else {
                                None
                            }.unwrap_or(Vec::new());
                            items.push(PathItem {
                                ident,
                                ty_args,
                            });
                        }
                        State::SepOrEnd
                    } else if let Some(next_ty_args) = self.maybe_path_ty_args()? {
                        let ty_args = std::mem::replace(&mut ty_args, next_ty_args);
                        if !ty_args.is_empty() {
                            if let Some(ident) = ident.take() {
                                items.push(PathItem {
                                    ident,
                                    ty_args,
                                });
                            } else {
                                // Misplaced ty args.
                                return self.fatal(ty_args[0].span, "unexpected type arguments");
                            }
                        }
                        State::SepOrEnd
                    } else {
                        let tok = self.nth(0);
                        if in_type_pos {
                            return self.fatal(tok.span,
                                &format!("expected type expression, found `{:?}`", tok.value));
                        } else {
                            return self.fatal(tok.span,
                                &format!("expected expression, found `{:?}`", tok.value));
                        }
                    }
                }
                State::SepOrEnd => {
                    let tok = self.nth(0);
                    match tok.value {
                        Token::ColonColon => {
                            self.consume();
                            State::IdentOrTyArgs
                        }
                        _ => {
                            if items.is_empty() && ident.is_none() {
                                return self.fatal(tok.span,
                                    &format!("unexpected {:?}", tok.value));
                            } else {
                                State::Done
                            }
                        }
                    }
                }
                State::Done => break,
            }
        }

        // Flush ident.
        if let Some(ident) = ident {
            items.push(PathItem {
                ident,
                ty_args: Vec::new(),
            });
        }

        let span_start = anchor.map(|v| v.span.start)
            .unwrap_or(items[0].ident.span.start);
        let last = items.last().unwrap();
        let span_end = last.ty_args.last()
            .map(|s| s.span.end)
            .unwrap_or(last.ident.span.end);
        Ok(Span::new(span_start, span_end).spanned(self.ast.insert_sym_path(SymPath {
            anchor,
            items,
        })))
    }

    fn maybe_as_ident(&mut self) -> PResult<Option<S<Ident>>> {
        Ok(if self.maybe(Token::Keyword(Keyword::As)).is_some() {
            Some(self.ident()?)
        } else {
            None
        })
    }

    fn path_terms(&mut self) -> PResult<S<Vec<S<PathTerm>>>> {
        let mut terms = Vec::new();
        let list = self.maybe(Token::BlockOpen(lex::Block::Brace));
        let mut span_end = None;
        loop {
            let tok = self.nth(0);
            let term = match tok.value {
                Token::Keyword(Keyword::SelfLower) if list.is_some() => {
                    self.consume();
                    let renamed_as = self.maybe_as_ident()?;
                    let span_end = renamed_as.as_ref().map(|v| v.span.end)
                        .unwrap_or(tok.span.end);
                    Span::new(tok.span.start, span_end).spanned(PathTerm::Self_(PathTermSelf {
                        renamed_as,
                    }))
                }
                Token::Star => {
                    self.consume();
                    tok.with_value(PathTerm::Star)
                }
                Token::Ident => {
                    // Is this a leaf?
                    if list.is_none() || self.nth(1).value != Token::ColonColon {
                        let ident = self.ident()?;
                        let renamed_as = self.maybe_as_ident()?;
                        let span_end = renamed_as.as_ref().map(|v| v.span.end)
                            .unwrap_or(tok.span.end);
                        Span::new(tok.span.start, span_end).spanned(PathTerm::Ident(PathTermIdent {
                            ident,
                            renamed_as,
                        }))
                    } else {
                        self.use_path()?.map(PathTerm::Path)
                    }
                }
                Token::BlockClose(lex::Block::Brace) => {
                    self.consume();
                    span_end = Some(tok.span.end);
                    break;
                }
                _ => {
                    return self.fatal(tok.span, &format!("unexpected {:?}", tok.value));
                }
            };
            terms.push(term);
            if list.is_none() {
                break;
            }

            if self.maybe(Token::Comma).is_none()
                && self.nth(0).value != Token::BlockClose(lex::Block::Brace)
            {
                return self.fatal(tok.span, &format!("unexpected {:?}", tok.value));
            }
        }
        let span_start = list.map(|v| v.span.start)
            .unwrap_or_else(|| terms.first().unwrap().span.start);
        let span_end = span_end.unwrap_or_else(|| terms.last().unwrap().span.end);
        Ok(Span::new(span_start, span_end).spanned(terms))
    }

    fn use_path(&mut self) -> PResult<S<NodeId>> {
        #[derive(Clone, Copy, Debug)]
        enum State {
            Done,
            IdentOrTerm,
            SepOrEnd,
        }

        let mut state = State::IdentOrTerm;

        let mut prefix = Vec::new();

        loop {
            match state {
                State::IdentOrTerm => {
                    if (self.nth(0).value, self.nth(1).value) == (Token::Ident, Token::ColonColon) {
                        let ident = self.ident()?;
                        prefix.push(ident);
                        state = State::SepOrEnd;
                    } else {
                        // This is a leaf, go parse terms.
                        state = State::Done;
                    }
                }
                State::SepOrEnd => {
                    let tok = self.next();
                    match tok.value {
                        Token::ColonColon => {
                            state = State::IdentOrTerm;
                        }
                        Token::Semi => {
                            state = State::Done;
                        }
                        _ => {
                            return self.fatal(tok.span,
                                &format!("unexpected {:?}", tok.value));
                        }
                    }
                }
                State::Done => break,
            }
        }

        let terms = self.path_terms()?;
        let span_start = prefix.first().map(|v| v.span.start)
            .unwrap_or(terms.span.start);
        Ok(Span::new(span_start, terms.span.end).spanned(self.ast.insert_use_path(UsePath {
            prefix,
            terms: terms.value,
        })))
    }

    fn maybe_path_ty_args(&mut self) -> PResult<Option<Vec<S<NodeId>>>> {
        if self.maybe(Token::Lt).is_none() {
            return Ok(None);
        }
        let mut ty_args = Vec::new();
        loop {
            ty_args.push(self.ty_expr()?);
            let mut tok = self.nth(0);
            // Split GtGt into Gt and Gt.
            if tok.value == Token::GtGt {
                self.consume();
                let i = tok.span.start;
                self.prepend_buf(S::new(Span::new(i, i + 1), Token::Gt));
                self.prepend_buf(S::new(Span::new(i + 1, i + 2), Token::Gt));

                tok = self.nth(0);
            }
            self.consume();
            match tok.value {
                Token::Comma => {}
                Token::Gt => {
                    break;
                }
                _ => {
                    return self.fatal(tok.span,
                        &format!("expected `,` or `>`, found {:?}", tok.value));
                }
            }
        }
        Ok(Some(ty_args))
    }

    fn maybe_formal_ty_args(&mut self) -> PResult<Vec<S<Ident>>> {
        let tok = self.nth(0);
        if tok.value != Token::Lt {
            return Ok(Vec::new());
        }

        let mut ty_args = Vec::new();

        self.consume();

        loop {
            let name = self.ident()?;
            ty_args.push(name);

            let seen_comma = self.maybe(Token::Comma).is_some();

            let tok = self.nth(0);
            match tok.value {
                Token::Gt => {
                    self.consume();
                    break;
                }
                _ if !seen_comma => {
                    return self.fatal(tok.span,
                        &format!("expected `,` or `>`, found {:?}", tok.value));
                }
                _ => {}
            }
        };
        Ok(ty_args)
    }

    fn maybe_block_expr(&mut self) -> PResult<Option<S<NodeId>>> {
        let decl_item = self.maybe_decl_item()?;
        if decl_item.is_some() {
            return Ok(decl_item);
        }

        let tok = self.nth(0);
        Ok(Some(match tok.value {
            Token::Keyword(Keyword::Let) => {
                let span_start = tok.span.start;
                self.consume();
                let muta = self.maybe(Token::Keyword(Keyword::Mut))
                    .map(|v| v.map(|_| {}));
                let name = self.ident()?;
                let ty = if self.maybe(Token::Colon).is_some() {
                    Some(self.ty_expr()?)
                } else {
                    None
                };
                let init = if self.maybe(Token::Eq).is_some() {
                    Some(self.expr(0)?)
                } else {
                    None
                };
                let span_end =
                    init.as_ref().map(|v| v.span.end)
                        .or(ty.as_ref().map(|v| v.span.end))
                        .unwrap_or(name.span.end);
                Span::new(span_start, span_end).spanned(self.ast.insert_var_decl(VarDecl {
                    muta,
                    name,
                    ty,
                    init,
                }))
            }
            _ => return Ok(None),
        }))
    }

    fn maybe_block(&mut self) -> PResult<Option<S<NodeId>>> {
        let tok = self.nth(0);
        if tok.value != Token::BlockOpen(lex::Block::Brace) {
            return Ok(None);
        }
        self.consume();
        let span_start = tok.span.start;

        let mut exprs = Vec::new();
        let span_end = loop {
            let expr = if let Some(v) = self.maybe_block_expr()? {
                Some(v)
            } else {
                self.maybe_expr()?
            };

            let semi = self.maybe(Token::Semi);
            let end = self.maybe(Token::BlockClose(lex::Block::Brace));

            let empty_expr = expr.is_none();
            if let Some(expr) = expr {
                exprs.push(expr);
            }

            if let Some(empty) = semi {
                // If we have empty expression in the middle of block or
                // semicolon at the end of the block, add an Empty node as expr.
                if empty_expr || end.is_some() {
                    exprs.push(empty.with_value(self.ast.insert_empty_node()));
                }
            }

            if let Some(end) = end {
                break end.span.end;
            }

            if semi.is_none() {
                let tok = self.nth(0);
                return self.fatal(tok.span,
                    &format!("expected `}}` or `;`, found {:?}", tok.value));
            }
        };

        Ok(Some(Span::new(span_start, span_end).spanned(self.ast.insert_block(Block {
            exprs,
        }))))
    }

    fn maybe_expr(&mut self) -> PResult<Option<S<NodeId>>> {
        let tok = self.nth(0);
        if is_expr_delim(tok.value) {
            return Ok(None);
        }
        self.expr(0).map(Some)
    }

    fn expr(&mut self, outer_prec: u32) -> PResult<S<NodeId>> {
        let tok = self.nth(0);
        // Handle prefix position.
        let mut left = match tok.value {
            Token::Minus => {
                self.consume();
                let arg = self.expr(150)?;
                Span::new(tok.span.start, arg.span.end)
                    .spanned(self.ast.insert_op(Op::Unary(UnaryOp {
                        kind: tok.span.spanned(UnaryOpKind::Neg),
                        arg,
                    })))
            }
            Token::Keyword(Keyword::False) | Token::Keyword(Keyword::True) => {
                self.consume();
                let v = tok.value == Token::Keyword(Keyword::True);
                tok.span.spanned(self.ast.insert_literal(Literal::Bool(v)))
            }
            Token::Literal(_) => {
                self.literal()?
            }
            // Expr grouping or tuple.
            Token::BlockOpen(lex::Block::Paren) => {
                self.consume();
                let expr = self.expr(0)?;
                self.expect(Token::BlockClose(lex::Block::Paren))?;
                expr
            }
            // Block
            Token::BlockOpen(lex::Block::Brace) => {
                self.maybe_block()?.unwrap()
            }
            _ => self.sym_path(false)?,
        };

        // Handle infix position.
        loop {
            let tok = self.nth(0);
            let prec = match tok.value {
                // Field access or method call
                Token::Dot => 180,
                // Free fn call
                Token::BlockOpen(lex::Block::Paren) => 170,
                Token::Keyword(Keyword::As) => 140,
                Token::Star | Token::Slash => 130,
                Token::Plus | Token::Minus => 120,
                _ => if is_expr_delim(tok.value) {
                    break;
                } else {
                    return self.fatal(tok.span, &format!("expected expression, found {:?}", tok.value));
                }
            };

            if outer_prec >= prec {
                break;
            }

            self.consume();
            left = match tok.value {
                Token::Star => {
                    let right = self.expr(prec)?;
                    left.span.extended(right.span.end).spanned(self.ast.insert_op(Op::BinaryOp(BinaryOp {
                        kind: tok.span.spanned(BinaryOpKind::Mul),
                        left,
                        right,
                    })))
                }
                Token::Slash => {
                    let right = self.expr(prec)?;
                    left.span.extended(right.span.end).spanned(self.ast.insert_op(Op::BinaryOp(BinaryOp {
                        kind: tok.span.spanned(BinaryOpKind::Div),
                        left,
                        right,
                    })))
                }
                Token::Plus => {
                    let right = self.expr(prec)?;
                    left.span.extended(right.span.end).spanned(self.ast.insert_op(Op::BinaryOp(BinaryOp {
                        kind: tok.span.spanned(BinaryOpKind::Add),
                        left,
                        right,
                    })))
                }
                Token::Minus => {
                    let right = self.expr(prec)?;
                    left.span.extended(right.span.end).spanned(self.ast.insert_op(Op::BinaryOp(BinaryOp {
                        kind: tok.span.spanned(BinaryOpKind::Sub),
                        left,
                        right,
                    })))
                }
                // Free fn call
                Token::BlockOpen(lex::Block::Paren) => {
                    self.fn_call(left.map(FnCallee::Expr), None)?
                        .map(|v| self.ast.insert_fn_call(v))
                }
                // Field access or method call
                Token::Dot => {
                    let ident = self.ident()?;
                    if self.maybe(Token::BlockOpen(lex::Block::Paren)).is_some() {
                        let callee = ident.span.spanned(FnCallee::Expr(
                            self.ast.insert_sym_path(SymPath::from_ident(ident))));
                        self.fn_call(callee, Some(left))?
                            .map(|v| self.ast.insert_fn_call(v))
                    } else {
                        left.span.extended(ident.span.end)
                            .spanned(self.ast.insert_field_access(FieldAccess {
                                receiver: left,
                                field: ident,
                            }))
                    }
                }
                Token::Keyword(Keyword::As) => {
                    let ty = self.ty_expr()?;
                    left.span.extended(ty.span.end).spanned(self.ast.insert_cast(Cast {
                        expr: left,
                        ty,
                    }))
                }
                _ => unreachable!(),
            }
        }
        Ok(left)
    }

    // Expects the opening paren to be already consumed.
    fn fn_call(&mut self, callee: S<FnCallee>, receiver: Option<S<NodeId>>)
        -> PResult<S<FnCall>>
    {
        let mut args = Vec::new();
        let kind = if let Some(receiver) = receiver {
            args.push(receiver);
            FnCallKind::Method
        } else {
            FnCallKind::Free
        };
        let span_end = loop {
            let arg = self.maybe_expr()?;
            if let Some(arg) = arg {
                args.push(arg);

                let tok = self.next();
                match tok.value {
                    Token::Comma => {},
                    Token::BlockClose(lex::Block::Paren) => break tok.span.end,
                    _ => return self.fatal(tok.span,
                        &format!("expected `,` or `)`, found {:?}", tok.value)),
                }
            } else {
                let tok = self.expect(Token::BlockClose(lex::Block::Paren))?;
                break tok.span.end;
            }
        };
        Ok(S {
            span: callee.span.extended(span_end),
            value: FnCall {
                callee,
                kind,
                args,
            }
        })
    }

    fn literal(&mut self) -> PResult<S<NodeId>> {
        let tok = self.nth(0);
        let kind = if let Token::Literal(v) = tok.value {
            v
        } else {
            return self.fatal(tok.span, &format!("expected literal, found {:?}", tok.value))?;
        };
        self.consume();
        let lit = match kind {
            lex::Literal::Int => {
                self.int_literal(tok.span)?
            }
            lex::Literal::String => {
                self.string_literal(tok.span)?
            }
            lex::Literal::Float => {
                self.float_literal(tok.span)?
            }
            lex::Literal::Char => {
                self.char_literal(tok.span)?
            }
        };
        Ok(tok.with_value(self.ast.insert_literal(lit)))
    }

    fn int_literal(&self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        match s.parse::<IntLiteral>() {
            Ok(v) => Ok(Literal::Int(v)),
            Err(_) => {
                self.fatal(span, "invalid integer literal")
            }
        }
    }

    fn float_literal(&self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        match s.parse::<FloatLiteral>() {
            Ok(v) => Ok(Literal::Float(v)),
            Err(_) => {
                self.fatal(span, "invalid floating point literal")
            }
        }
    }

    fn string_literal(&mut self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        match lex::string_literal(s) {
            Ok(s) => Ok(Literal::String(s)),
            Err(lex::StringLiteralError { pos, kind }) => {
                let span = Span::new(pos, pos + 1);
                match kind {
                    lex::StringErrorKind::BadEscape => self.fatal(span, "invalid string escape"),
                    lex::StringErrorKind::BadUnicodeEscape => self.fatal(span, "invalid string unicode escape"),
                }
            }
        }
    }

    fn char_literal(&mut self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        // match lex::string_literal(s) {
        //     Ok(s) => Ok(Literal::String(s)),
        //     Err(lex::StringError { pos, kind }) => {
        //         let span = Span::new(pos, pos + 1);
        //         match kind {
        //             lex::StringErrorKind::BadEscape => self.fatal(span, "invalid string escape"),
        //         }
        //     }
        // }
        unimplemented!()
    }
}

fn parse_file_with(path: impl AsRef<Path>, fs: &mut dyn Fs) -> PResult<Ast> {
    let path = path.as_ref();
    let mut ast = Ast::new();
    let s = Parser::read_file(fs, path)?;
    Parser::new(&s, None, path.to_path_buf(), fs, &mut ast).parse()?;
    Ok(ast)
}

pub fn parse_file(path: impl AsRef<Path>) -> PResult<Ast> {
    struct StdFs;
    impl Fs for StdFs {
        fn read_file(&mut self, path: &Path) -> io::Result<String> {
            std::fs::read_to_string(path)
        }
    }
    parse_file_with(path, &mut StdFs)
}

pub fn parse_str(s: &str) -> PResult<Ast> {
    struct NotFoundFs;
    impl Fs for NotFoundFs {
        fn read_file(&mut self, _path: &Path) -> io::Result<String> {
            Err(io::Error::new(io::ErrorKind::NotFound, "not found"))
        }
    }

    let mut ast = Ast::new();
    Parser::new(&s, None, "unnamed.tsr".into(), &mut NotFoundFs, &mut ast).parse()?;
    Ok(ast)
}

fn is_expr_delim(tok: Token) -> bool {
    match tok {
        | Token::BlockClose(_)
        | Token::Comma
        | Token::Semi
        => true,
        _ => false,
    }
}