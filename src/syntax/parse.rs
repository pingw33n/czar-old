#[cfg(test)]
mod test;

use std::convert::TryFrom;
use std::sync::Arc;

use crate::diag::{self, Diag};
use crate::hir::{*, Range};

use super::*;

#[derive(Debug)]
pub enum ErrorKind {
    Io(io::Error),
    Lex,
    Parse,
}

#[derive(Debug)]
struct PError {
    kind: ErrorKind,
    backtrace: Option<Box<backtrace::Backtrace>>,
}

impl From<ErrorKind> for PError {
    fn from(kind: ErrorKind) -> Self {
        let backtrace = if false && cfg!(debug_assertions) {
            Some(Box::new(backtrace::Backtrace::new()))
        } else {
            None
        };
        Self {
            kind,
            backtrace,
        }
    }
}

type PResult<T> = std::result::Result<T, PError>;

pub trait Fs {
    fn read_file(&mut self, path: &StdPath) -> io::Result<String>;
}

#[derive(Clone, Copy)]
struct PrecAssoc {
    prec: u32,

    /// `assoc == 0` => right-assoc
    ///  `assoc == 1` => left-assoc
    assoc: u32,
}

const NAMED_STRUCT_VALUE_PREC: PrecAssoc = PrecAssoc { prec: 10000, assoc: 1 };
const FIELD_ACCESS_PREC: PrecAssoc = PrecAssoc { prec: 180, assoc: 1 };
const FN_CALL_PREC: PrecAssoc = PrecAssoc { prec: 170, assoc: 1 };
const UNWRAP_PREC: PrecAssoc = PrecAssoc { prec: 160, assoc: 1 };
const UNARY_PREC: PrecAssoc = PrecAssoc { prec: 150, assoc: 1 };
const AS_PREC: PrecAssoc = PrecAssoc { prec: 140, assoc: 1 };
const MUL_PREC: PrecAssoc = PrecAssoc { prec: 130, assoc: 1 };
const PLUS_PREC: PrecAssoc = PrecAssoc { prec: 120, assoc: 1 };
const SHIFT_PREC: PrecAssoc = PrecAssoc { prec: 110, assoc: 1 };
const BIT_AND_PREC: PrecAssoc = PrecAssoc { prec: 100, assoc: 1 };
const BIT_XOR_PREC: PrecAssoc = PrecAssoc { prec: 90, assoc: 1 };
const BIT_OR_PREC: PrecAssoc = PrecAssoc { prec: 80, assoc: 1 };
const CMP_PREC: PrecAssoc = PrecAssoc { prec: 70, assoc: 1 };
const AND_PREC: PrecAssoc = PrecAssoc { prec: 60, assoc: 1 };
const OR_PREC: PrecAssoc = PrecAssoc { prec: 50, assoc: 1 };
const RANGE_PREC: PrecAssoc = PrecAssoc { prec: 40, assoc: 1 };
const ASSIGN_PREC: PrecAssoc = PrecAssoc { prec: 30, assoc: 0 };

#[derive(Clone, Copy)]
struct ExprState {
    min_prec: u32,

    /// Whether the expr parser recognizes struct constructors.
    parse_struct_value: bool,

    /// Are we immediately after '{' or '('?
    at_group_start: bool,
}

impl ExprState {
    fn with_min_prec(self, min_prec: u32) -> Self {
        Self {
            min_prec,
            ..self
        }
    }

    fn with_at_group_start(self, at_group_start: bool) -> Self {
        Self {
            at_group_start,
            ..self
        }
    }
}

impl Default for ExprState {
    fn default() -> Self {
        Self {
            min_prec: 0,
            parse_struct_value: true,
            at_group_start: false,
        }
    }
}

struct ParserImpl<'a> {
    s: &'a str,
    lex: Lexer<'a>,
    hir: &'a mut Hir,
    source_id: SourceId,
    fs: &'a mut dyn Fs,
    diag: &'a mut Diag,
}

impl<'a> ParserImpl<'a> {
    fn new(
        s: &'a str,
        source_id: SourceId,
        fs: &'a mut dyn Fs,
        hir: &'a mut Hir,
        diag: &'a mut Diag,
    ) -> Self {
        Self {
            s,
            lex: Lexer::new(s),
            hir,
            source_id,
            fs,
            diag,
        }
    }

    fn parse(mut self) -> PResult<()> {
        let root = self.module_inner(Some(self.source_id), 0, None)?;
        self.hir.root = root;
        if self.lex.errors().is_empty() {
            Ok(())
        } else {
            Err(ErrorKind::Lex.into())
        }
    }

    fn maybe_vis(&mut self) -> Option<S<Vis>> {
        let publ = self.lex.maybe(Token::Keyword(Keyword::Pub))?.map(|_| {});
        let restrict = if self.lex.maybe(Token::BlockOpen(lex::Block::Paren)).is_some() {
            unimplemented!();
        } else {
            None
        };
        Some(publ.span.spanned(Vis {
            restrict,
        }))
    }

    fn maybe_item(&mut self, top_level: bool) -> PResult<Option<NodeId>> {
        let vis = self.maybe_vis();
        let tok0 = self.lex.nth(0);
        Ok(Some(match tok0.value {
            Token::Keyword(Keyword::Unsafe) => {
                let tok1 = self.lex.nth(1);
                match tok1.value {
                    Token::Keyword(Keyword::Fn) => self.fn_(vis)?,
                    Token::Keyword(Keyword::Static) => unimplemented!(),
                    _ => {
                        return self.error(tok1.span,
                            format!("expected `fn` or `static`, found `{}`", tok1.value));
                    }
                }
            }
            Token::Keyword(Keyword::Fn) => self.fn_(vis)?,
            Token::Keyword(Keyword::Mod) => self.module(top_level, vis)?,
            Token::Keyword(Keyword::Static) => unimplemented!(),
            Token::Keyword(Keyword::Use) => self.use_(vis)?,
            Token::Keyword(Keyword::Struct) => self.struct_(vis)?,
            Token::Keyword(Keyword::Impl) => {
                if let Some(vis) = vis {
                    return self.error(vis.span, "invalid visibility for impl block".into())
                }
                self.impl_()?
            }
            _ => {
                if let Some(vis) = vis {
                    return self.error(vis.span,
                        format!("expected item after visibility modifier, found `{}`", tok0.value));
                }
                return Ok(None);
            }
        }))
    }

    fn module_inner(&mut self,
        source_id: Option<SourceId>,
        start: usize,
        name: Option<ModuleName>,
    ) -> PResult<NodeId> {
        let mut items = Vec::new();
        let end = loop {
            if let Some(item) = self.maybe_item(source_id.is_some())? {
                items.push(item);
            } else {
                let tok = self.lex.nth(0);
                if name.is_none() && tok.value != Token::Eof
                    || name.is_some() && tok.value != Token::BlockClose(lex::Block::Brace)
                {
                    return self.error(tok.span,
                        format!("expected item, found `{}`", tok.value));
                }
                break tok.span.end;
            }
        };
        Ok(self.hir.insert_module(Span::new(start, end).spanned(Module {
            source_id,
            name,
            items,
        })))
    }

    fn module(&mut self, top_level: bool, vis: Option<S<Vis>>) -> PResult<NodeId> {
        let mod_ = self.expect(Token::Keyword(Keyword::Mod))?;
        let start = vis.as_ref().map(|v| v.span.start)
            .unwrap_or(mod_.span.start);
        let name = self.ident()?;
        let name = ModuleName {
            name,
            vis,
        };

        Ok(if self.lex.nth(0).value == Token::Semi {
            let end = self.lex.next().span.end;

            let (path, text) = {
                let source = &self.hir.sources()[self.source_id];
                let mut path = source.path.to_path_buf();
                assert!(path.pop());
                if top_level {
                    if let Some(mod_name) = &source.mod_name {
                        path.push(mod_name.as_str());
                    }
                } else {
                    return self.error(Span::new(start, end),
                        "module file reference can be top level only".into());
                }
                path.push(source_file_name(&name.name.value));
                let text = Arc::new(read_file(self.fs, &path)?);
                (path, text)
            };
            let source_id = self.hir.sources_mut().insert(Source {
                mod_name: Some(name.name.value.clone()),
                path,
                text: text.clone(),
            });

            ParserImpl::new(&text, source_id, self.fs, self.hir, self.diag).parse()?;
            let r = std::mem::replace(&mut self.hir.root, NodeId::null());
            assert_ne!(r, NodeId::null());
            r
        } else {
            self.expect(Token::BlockOpen(lex::Block::Brace))?;
            let r = self.module_inner(None, start, Some(name))?;
            self.expect(Token::BlockClose(lex::Block::Brace))?;
            r
        })
    }

    // use <path>;
    fn use_(&mut self, vis: Option<S<Vis>>) -> PResult<NodeId> {
        let start = self.expect(Token::Keyword(Keyword::Use))?.span.start;
        let anchor = self.maybe_path_anchor()?;
        let segment = self.use_path_segment()?;
        self.expect(Token::Semi)?;
        let segment_span = self.hir.node_kind(segment).span;
        let path_start = anchor.map(|v| v.span.start)
            .unwrap_or(segment_span.start);
        let path = self.hir.insert_path(Span::new(path_start, segment_span.end).spanned(
            Path {
                anchor,
                segment
            }));
        Ok(self.hir.insert_use(Span::new(start, segment_span.end).spanned(
            Use {
                vis,
                path,
            })))
    }

    fn error<T>(&mut self, span: Span, text: String) -> PResult<T> {
        let report = diag::Report {
            severity: diag::Severity::Error,
            text,
            source: Some(diag::Source {
                id: self.source_id,
                span,
            })
        };
        self.diag.report(report);
        Err(ErrorKind::Parse.into())
    }

    fn fn_(&mut self, vis: Option<S<Vis>>) -> PResult<NodeId> {
        let unsafe_ = self.lex.maybe(Token::Keyword(Keyword::Unsafe))
            .map(|v| v.map(|_| {}));

        let tok = self.expect(Token::Keyword(Keyword::Fn))?;
        let start = vis.as_ref().map(|v| v.span.start)
            .or(unsafe_.as_ref().map(|v| v.span.start))
            .unwrap_or(tok.span.start);

        let name = self.ident()?;
        let ty_args = self.maybe_formal_ty_args()?;

        let mut args = Vec::new();
        self.expect(Token::BlockOpen(lex::Block::Paren))?;
        let mut delimited = true;
        let mut variadic = None;
        while self.lex.nth(0).value != Token::BlockClose(lex::Block::Paren) {
            if !delimited {
                let tok = self.lex.nth(0);
                return self.error(tok.span, format!("expected `,` but found `{}`", tok.value));
            }
            if variadic.is_some() {
                let tok = self.lex.nth(0);
                return self.error(tok.span, format!("expected `)`, found `{}`", tok.value));
            }

            if self.lex.nth(0).value == Token::DotDotDot {
                let tok = self.lex.next();
                variadic = Some(tok.map(|_| {}));
            } else {
                let arg = if args.is_empty() {
                    let ref_ = self.lex.maybe(Token::Amp);
                    let mut_ = self.lex.maybe(Token::Keyword(Keyword::Mut));
                    let self_ = self.lex.maybe(Token::Keyword(Keyword::SelfLower));
                    if (ref_.is_some() || mut_.is_some()) && self_.is_none() {
                        let tok = self.lex.nth(0);
                        return self.error(tok.span, format!("expected `self`, found `{}`", tok.value));
                    }
                    if let Some(self_) = self_ {
                        let ty = self.hir.insert_path_from_ident(self_.with_value(Ident::self_upper()));
                        let mut ty = self.hir.insert_ty_expr(
                            Span::new(mut_.map(|v| v.span.start).unwrap_or(self_.span.start), self_.span.end).spanned(TyExpr {
                                muta: mut_.map(|v| v.with_value(())),
                                data: self_.with_value(TyData::Path(ty)),
                            }));
                        if let Some(ref_) = ref_ {
                            ty = self.hir.insert_ty_expr(
                                Span::new(ref_.span.start, self_.span.end).spanned(TyExpr {
                                    muta: None,
                                    data: ref_.with_value(TyData::Ref(ty))
                                }));
                        }
                        Some(FnDeclArg {
                            pub_name: self_.with_value(None),
                            priv_name: self_.with_value(Ident::self_lower()),
                            ty,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                };
                let arg = if let Some(arg) = arg {
                    arg
                } else {
                    let (pub_name, priv_name) = if let Some(underscore) = self.lex.maybe(Token::Keyword(Keyword::Underscore)) {
                        let priv_name = self.ident()?;
                        (underscore.with_value(None), priv_name)
                    } else {
                        let pub_name = self.ident()?;
                        let priv_name = self.maybe_ident()?.unwrap_or_else(|| pub_name.clone());
                        (pub_name.map(Some), priv_name)
                    };
                    self.expect(Token::Colon)?;
                    let ty = self.ty_expr()?;
                    FnDeclArg { pub_name, priv_name, ty }
                };
                let start = arg.pub_name.span.start;
                let end = self.hir.node_kind(arg.ty).span.end;
                args.push(self.hir.insert_fn_decl_arg(Span::new(start, end).spanned(arg)));
            }

            delimited = self.lex.maybe(Token::Comma).is_some();
        }
        assert_eq!(self.lex.next().value, Token::BlockClose(lex::Block::Paren));

        let ret_ty = if self.lex.maybe(Token::RArrow).is_some() {
            Some(self.ty_expr()?)
        } else {
            None
        };

        let body = if let Some(tok) = self.lex.maybe(Token::BlockOpen(lex::Block::Brace)) {
            Some(self.block_inner(tok.span.start)?)
        } else {
            None
        };
        let end = if let Some(body) = body {
            self.hir.node_kind(body).span.end
        } else {
            self.expect(Token::Semi)?.span.end
        };

        let span = Span::new(start, end);
        Ok(self.hir.insert_fn_decl(span.spanned(FnDecl {
            name,
            vis,
            ty_args,
            args,
            ret_ty,
            unsafe_,
            variadic,
            body,
        })))
    }

    fn expect(&mut self, tok: Token) -> PResult<S<Token>> {
        let actual = self.lex.next();
        if actual.value == tok {
            Ok(actual)
        } else {
            self.error(actual.span, format!("expected `{}` but found `{}`", tok, actual.value))
        }
    }

    fn ident(&mut self) -> PResult<S<Ident>> {
        let tok = self.expect(Token::Ident)?;
        self.make_ident(tok.span)
    }

    fn maybe_ident(&mut self) -> PResult<Option<S<Ident>>> {
        Ok(if let Some(tok) = self.lex.maybe(Token::Ident) {
            Some(self.make_ident(tok.span)?)
        } else {
            None
        })
    }

    fn make_ident(&mut self, span: Span) -> PResult<S<Ident>> {
        let s = &self.s[span.range()];
        let value = lex::ident(s);
        if value.is_empty() {
            self.error(span, "missing raw identifier or raw string".into())
        } else {
            match value.as_str() {
                "_" | "self" | "Self" => return self.error(span, "invalid raw identifier".into()),
                _ => {}
            }
            Ok(span.spanned(value.into()))
        }
    }

    // foo<T>
    // foo<T>::bar<U>
    // foo<T>::bar<U>::baz<V>
    fn ty_expr(&mut self) -> PResult<NodeId> {
        let muta = self.lex.maybe(Token::Keyword(Keyword::Mut))
            .map(|tok| tok.map(|_| {}));
        let tok = self.lex.nth(0);
        let start = muta.map(|s| s.span.start)
            .unwrap_or(tok.span.start);

        let (end, data) = match tok.value {
            Token::Amp | Token::AmpAmp => {
                self.lex.consume();
                let ty = self.ty_expr()?;
                let end = self.hir.node_kind(ty).span.end;
                let span = Span::new(tok.span.start + 1, end);
                let data = if tok.value == Token::AmpAmp {
                    TyData::Ref(self.hir.insert_ty_expr(span.spanned(TyExpr {
                        muta: None,
                        data: span.spanned(TyData::Ref(ty)),
                    })))
                } else {
                    TyData::Ref(ty)
                };
                (end, data)
            }
            Token::Star => {
                self.lex.consume();
                let ty = self.ty_expr()?;
                (self.hir.node_kind(ty).span.end, TyData::Ptr(ty))
            },
            Token::BlockOpen(lex::Block::Bracket) => {
                self.lex.consume();
                let ty = self.ty_expr()?;
                let data = if self.lex.maybe(Token::Semi).is_some() {
                    let len = self.expr(Default::default())?;
                    TyData::Array(Array {
                        ty,
                        len,
                    })
                } else {
                    // [<ty>*]
                    let resizable = self.lex.maybe(Token::Star).is_some();
                    TyData::Slice(Slice {
                        ty,
                        resizable,
                    })
                };
                let end = self.expect(Token::BlockClose(lex::Block::Bracket))?.span.end;
                (end, data)
            }
            Token::BlockOpen(lex::Block::Brace) => {
                let struct_ = self.struct_type(false)?;
                (self.hir.node_kind(struct_).span.end, TyData::Struct(struct_))
            }
            _ => {
                let path = self.sym_path(true)?;
                (self.hir.node_kind(path).span.end, TyData::Path(path))
            }
        };
        let data = Span::new(tok.span.start, end).spanned(data);
        Ok(self.hir.insert_ty_expr(Span::new(start, end).spanned(TyExpr { muta, data })))
    }

    fn maybe_path_anchor(&mut self) -> PResult<Option<S<PathAnchor>>> {
        let tok = self.lex.nth(0);

        let mut span_end = tok.span.end;
        let r = if tok.value == Token::Keyword(Keyword::Super) {
            let mut count = 1;
            loop {
                self.lex.consume();

                if self.lex.nth(0).value != Token::ColonColon {
                    break;
                }

                let tok = self.lex.nth(1);
                if tok.value != Token::Keyword(Keyword::Super) {
                    break;
                }
                self.lex.consume();
                span_end = tok.span.end;
                count += 1;
            }
            Span::new(tok.span.start, span_end).spanned(PathAnchor::Super { count })
        } else {
            tok.with_value(match tok.value {
                Token::ColonColon => {
                    self.lex.consume();
                    PathAnchor::Root
                }
                Token::Keyword(Keyword::Package) => {
                    self.lex.consume();
                    PathAnchor::Package
                }
                _ => return Ok(None),
            })
        };
        if !matches!(r.value, PathAnchor::Root) {
            self.expect(Token::ColonColon)?;
        }
        Ok(Some(r))
    }

    fn sym_path(&mut self, in_type_pos: bool) -> PResult<NodeId> {
        if let Some(v) = self.maybe_sym_path(in_type_pos)? {
            Ok(v)
        } else {
            let tok = self.lex.nth(0);
            return self.error(tok.span, format!("expected symbol path, found `{}`", tok.value));
        }
    }

    fn maybe_sym_path(&mut self, in_type_pos: bool) -> PResult<Option<NodeId>> {
        let anchor = self.maybe_path_anchor()?;

        let mut items = Vec::new();

        loop {
            let tok = self.lex.nth(0);
            let ident = match tok.value {
                Token::Keyword(Keyword::SelfLower) => {
                    self.lex.consume();
                    tok.span.spanned(Ident::self_lower())
                }
                Token::Keyword(Keyword::SelfUpper) => {
                    self.lex.consume();
                    tok.span.spanned(Ident::self_upper())
                }
                _ => {
                    if let Some(v) = self.maybe_ident()? {
                        v
                    } else if items.is_empty() {
                        return Ok(None);
                    } else {
                        let tok = self.lex.nth(0);
                        return self.error(tok.span, format!("expected ident, found `{}`", tok.value));
                    }
                }
            };

            let ty_args = if self.lex.nth(0).value == Token::Lt {
                // FIXME remove added HIR nodes when restoring state
                let save = self.save_state();
                match self.path_ty_args() {
                    Ok(ty_args) => {
                        assert!(!ty_args.is_empty());
                        if !in_type_pos {
                            let tok = self.lex.nth(0);
                            match tok.value {
                                | Token::BlockOpen(_)
                                | Token::BlockClose(_)
                                | Token::Semi
                                | Token::ColonColon
                                | Token::Comma
                                | Token::Dot
                                => {
                                    self.discard_state(save);
                                    Ok(ty_args)
                                }
                                _ => {
                                    self.restore_state(save);
                                    Err(())
                                }
                            }
                        } else {
                            self.discard_state(save);
                            Ok(ty_args)
                        }
                    }
                    Err(e) => {
                        if in_type_pos {
                            self.discard_state(save);
                            return Err(e);
                        }
                        self.restore_state(save);
                        Err(())
                    }
                }
            } else {
                Ok(Vec::new())
            };

            let done = ty_args.is_err();
            items.push(PathItem {
                ident,
                ty_args: ty_args.unwrap_or_default(),
            });

            if done || self.lex.maybe(Token::ColonColon).is_none() {
                break;
            }
        }

        Ok(Some(self.hir.insert_path_from_items(anchor, items)))
    }

    fn maybe_as_ident(&mut self) -> PResult<Option<S<Ident>>> {
        Ok(if self.lex.maybe(Token::Keyword(Keyword::As)).is_some() {
            Some(self.ident()?)
        } else {
            None
        })
    }

    fn path_end_ident_inner(&mut self, ident: S<Ident>) -> PResult<NodeId> {
        let renamed_as = self.maybe_as_ident()?;
        let end = renamed_as.as_ref().map(|v| v.span.end)
            .unwrap_or(ident.span.end);
        Ok(self.hir.insert_path_end_ident(Span::new(ident.span.start, end).spanned(
            PathEndIdent {
                item: PathItem {
                    ident,
                    ty_args: Vec::new(),
                },
                renamed_as,
            })))
    }

    fn path_suffix(&mut self) -> PResult<S<Vec<NodeId>>> {
        let mut suffix = Vec::new();
        let list = self.lex.maybe(Token::BlockOpen(lex::Block::Brace));
        let end = loop {
            let tok = self.lex.nth(0);
            let item = match tok.value {
                Token::Keyword(Keyword::SelfLower) if list.is_some() => {
                    self.lex.consume();
                    self.path_end_ident_inner(tok.span.spanned(Ident::self_lower()))?
                }
                Token::Star => {
                    self.lex.consume();
                    self.hir.insert_path_end_star(tok.span)
                }
                Token::Ident => {
                    // Is this a leaf?
                    if list.is_none() || self.lex.nth(1).value != Token::ColonColon {
                        let ident = self.ident()?;
                        self.path_end_ident_inner(ident)?
                    } else {
                        self.use_path_segment()?
                    }
                }
                Token::BlockClose(lex::Block::Brace) => {
                    self.lex.consume();
                    break Some(tok.span.end);
                }
                _ => {
                    return self.error(tok.span, format!("unexpected {}", tok.value));
                }
            };
            suffix.push(item);
            if list.is_none() {
                break None;
            }

            if self.lex.maybe(Token::Comma).is_none()
                && self.lex.nth(0).value != Token::BlockClose(lex::Block::Brace)
            {
                return self.error(tok.span, format!("unexpected `{}`", tok.value));
            }
        };
        if suffix.is_empty() {
            suffix.push(self.hir.insert_path_end_empty(Span::new(list.unwrap().span.start, end.unwrap())));
        }
        let start = list.map(|v| v.span.start)
            .unwrap_or_else(|| self.hir.node_kind(*suffix.first().unwrap()).span.start);
        let end = end.unwrap_or_else(|| self.hir.node_kind(*suffix.last().unwrap()).span.end);
        Ok(Span::new(start, end).spanned(suffix))
    }

    fn use_path_segment(&mut self) -> PResult<NodeId> {
        #[derive(Clone, Copy, Debug)]
        enum State {
            Done,
            IdentOrSuffix,
            SepOrEnd,
        }

        let mut state = State::IdentOrSuffix;

        let mut prefix = Vec::new();

        loop {
            match state {
                State::IdentOrSuffix => {
                    if (self.lex.nth(0).value, self.lex.nth(1).value) == (Token::Ident, Token::ColonColon) {
                        let ident = self.ident()?;
                        prefix.push(PathItem {
                            ident,
                            ty_args: Vec::new(),
                        });
                        state = State::SepOrEnd;
                    } else {
                        // This is a leaf, go parse suffix.
                        state = State::Done;
                    }
                }
                State::SepOrEnd => {
                    let tok = self.lex.next();
                    match tok.value {
                        Token::ColonColon => {
                            state = State::IdentOrSuffix;
                        }
                        Token::Semi => {
                            state = State::Done;
                        }
                        _ => {
                            return self.error(tok.span,
                                format!("unexpected `{}`", tok.value));
                        }
                    }
                }
                State::Done => break,
            }
        }

        let suffix = self.path_suffix()?;
        let span_start = prefix.first().map(|v| v.ident.span.start)
            .unwrap_or(suffix.span.start);
        Ok(self.hir.insert_path_segment(Span::new(span_start, suffix.span.end).spanned(
            PathSegment {
                prefix,
                suffix: suffix.value,
            })))
    }

    fn path_ty_args(&mut self) -> PResult<Vec<NodeId>> {
        self.expect(Token::Lt)?;
        let mut ty_args = Vec::new();
        loop {
            ty_args.push(self.ty_expr()?);
            let mut tok = self.lex.nth(0);
            // Split GtGt into Gt and Gt.
            if tok.value == Token::GtGt {
                self.lex.consume();
                let i = tok.span.start;
                self.lex.insert(S::new(Span::new(i, i + 1), Token::Gt));
                self.lex.insert(S::new(Span::new(i + 1, i + 2), Token::Gt));

                tok = self.lex.nth(0);
            }
            self.lex.consume();
            match tok.value {
                Token::Comma => {}
                Token::Gt => {
                    break;
                }
                _ => {
                    return self.error(tok.span,
                        format!("expected `,` or `>`, found `{}`", tok.value));
                }
            }
        }
        Ok(ty_args)
    }

    fn maybe_formal_ty_args(&mut self) -> PResult<Vec<NodeId>> {
        let tok = self.lex.nth(0);
        if tok.value != Token::Lt {
            return Ok(Vec::new());
        }

        let mut ty_args = Vec::new();

        self.lex.consume();

        loop {
            let name = self.ident()?;
            ty_args.push(self.hir.insert_type_arg(name.span.spanned(TypeArg {
                name,
            })));

            let seen_comma = self.lex.maybe(Token::Comma).is_some();

            let tok = self.lex.nth(0);
            match tok.value {
                Token::Gt => {
                    self.lex.consume();
                    break;
                }
                _ if !seen_comma => {
                    return self.error(tok.span,
                        format!("expected `,` or `>`, found `{}`", tok.value));
                }
                _ => {}
            }
        };
        Ok(ty_args)
    }

    fn block(&mut self) -> PResult<NodeId> {
        let tok = self.expect(Token::BlockOpen(lex::Block::Brace))?;
        self.block_inner(tok.span.start)
    }

    // Expects '{' to be already consumed.
    fn block_inner(&mut self, start: usize) -> PResult<NodeId> {
        let mut exprs = Vec::new();
        let end = loop {
            let expr = if let Some(v) = self.maybe_item(false)? {
                Some(v)
            } else {
                self.maybe_expr(ExprState {
                    at_group_start: true,
                    ..Default::default()
                })?
            };

            let semi = self.lex.maybe(Token::Semi);
            let end = self.lex.maybe(Token::BlockClose(lex::Block::Brace));

            if let Some(expr) = expr {
                exprs.push(expr);
            }

            if let Some(semi) = semi {
                // If we have empty expression in the middle of block or
                // semicolon at the end of the block, add an empty unnamed struct.
                if expr.is_none() || end.is_some() {
                    exprs.push(self.hir.insert_struct_value(semi.span.spanned(StructValue {
                        name: None,
                        explicit_tuple: None,
                        fields: Vec::new(),
                    })));
                }
            }

            if let Some(end) = end {
                break end.span.end;
            }

            if semi.is_none() &&
                expr.map(|v| needs_trailing_semi(self.hir.node_kind(v).value)).unwrap_or(true)
            {
                let tok = self.lex.nth(0);
                return self.error(tok.span,
                    format!("expected expression, found `{}`", tok.value));
            }
        };

        Ok(self.hir.insert_block(Span::new(start, end).spanned(Block {
            exprs,
        })))
    }

    fn unary_op(&mut self, span: Span, kind: UnaryOpKind, state: ExprState) -> PResult<NodeId> {
        let arg = self.expr(state.with_min_prec(UNARY_PREC.prec))?;
        Ok(self.hir.insert_op(Span::new(span.start, self.hir.node_kind(arg).span.end).spanned(
            Op::Unary(UnaryOp {
                kind: span.spanned(kind),
                arg,
            }))))
    }

    fn binary_op(&mut self,
        span: Span,
        left: NodeId,
        kind: BinaryOpKind,
        state: ExprState,
    ) -> PResult<NodeId> {
        let right = self.expr(state)?;
        let start = self.hir.node_kind(left).span.start;
        let end = self.hir.node_kind(right).span.end;
        Ok(self.hir.insert_op(Span::new(start, end).spanned(
            Op::Binary(BinaryOp {
                kind: span.spanned(kind),
                left,
                right,
            }))))
    }

    fn check_assoc_defined(&mut self, left: NodeId, op: S<Token>, f: impl Fn(BinaryOpKind) -> bool)
        -> PResult<()>
    {
        if self.hir.try_op(left)
            .and_then(|n| n.as_binary())
            .filter(|b| f(b.kind.value))
            .is_some()
        {
            self.error(op.span, format!("associativity is not defined for `{}`", op.value))
        } else {
            Ok(())
        }
    }

    fn expr(&mut self, state: ExprState) -> PResult<NodeId> {
        if let Some(v) = self.maybe_expr(state)? {
            Ok(v)
        } else {
            let tok = self.lex.nth(0);
            return self.error(tok.span, format!("expected expression, found `{}`", tok.value));
        }
    }

    /// `allow_struct_value` allows struct constructors.
    fn maybe_expr(&mut self, state: ExprState) -> PResult<Option<NodeId>> {
        let tok = self.lex.nth(0);
        // Handle prefix position.
        let mut left = match tok.value {
            Token::Minus => {
                self.lex.consume();
                self.unary_op(tok.span, UnaryOpKind::Neg, state)?
            }
            Token::Star => {
                self.lex.consume();
                self.unary_op(tok.span, UnaryOpKind::Deref, state)?
            }
            Token::Amp | Token::AmpAmp => {
                self.lex.consume();
                if tok.value == Token::AmpAmp {
                    self.lex.insert(Span::new(tok.span.start + 1, tok.span.end).spanned(Token::Amp));
                }
                let (kind, span) = if let Some(muta) = self.lex.maybe(Token::Keyword(Keyword::Mut)) {
                    (UnaryOpKind::AddrMut, tok.span.extended(muta.span.end))
                } else {
                    (UnaryOpKind::Addr, tok.span)
                };
                self.unary_op(span, kind, state)?
            }
            Token::Excl => {
                self.lex.consume();
                self.unary_op(tok.span, UnaryOpKind::Not, state)?
            }
            Token::Keyword(Keyword::Break) => {
                self.lex.consume();
                let label = self.lex.maybe(Token::Label)
                    .map(|t| t.span.spanned(lex::label(&self.s[t.span.range()])));
                let value = self.maybe_expr(Default::default())?;
                let span_end = label.as_ref().map(|t| t.span.end)
                    .or(value.map(|v| self.hir.node_kind(v).span.end))
                    .unwrap_or(tok.span.end);
                self.hir.insert_block_flow_ctl(tok.span.extended(span_end).spanned(BlockFlowCtl {
                    kind: BlockFlowCtlKind::Break,
                    label,
                    value,
                }))
            }
            Token::Keyword(Keyword::Continue) => {
                self.lex.consume();
               self.hir.insert_block_flow_ctl(tok.span.spanned(BlockFlowCtl {
                    kind: BlockFlowCtlKind::Continue,
                    label: None,
                    value: None,
                }))
            }
            Token::Keyword(Keyword::Return) => {
                self.lex.consume();
                let value = self.maybe_expr(Default::default())?;
                let span_end = value.map(|v| self.hir.node_kind(v).span.end)
                    .unwrap_or(tok.span.end);

                self.hir.insert_block_flow_ctl(tok.span.extended(span_end).spanned(BlockFlowCtl {
                    kind: BlockFlowCtlKind::Return,
                    label: None,
                    value,
                }))
            }
            Token::Keyword(Keyword::False) | Token::Keyword(Keyword::True) => {
                self.lex.consume();
                let v = tok.value == Token::Keyword(Keyword::True);
                self.hir.insert_literal(tok.span.spanned(Literal::Bool(v)))
            }
            Token::Literal(_) => {
                self.literal()?
            }
            Token::BlockOpen(lex::Block::Paren) => {
                self.lex.consume();

                let expr = self.expr(ExprState {
                    at_group_start: true,
                    ..Default::default()
                })?;
                self.expect(Token::BlockClose(lex::Block::Paren))?;
                expr
            }
            // Block or unnamed struct
            Token::BlockOpen(lex::Block::Brace) => {
                self.lex.consume();
                if state.parse_struct_value {
                    self.block_or_struct(None, tok.span.start)
                } else {
                    self.block_inner(tok.span.start)
                }?
            }
            // Start-unbounded range
            Token::DotDot | Token::DotDotEq => {
                self.lex.consume();
                let kind = if tok.value == Token::DotDot {
                    RangeKind::Exclusive
                } else {
                    RangeKind::Inclusive
                };
                let end = self.maybe_expr(Default::default())?;
                let span_end = end.map(|v| self.hir.node_kind(v).span.end)
                    .unwrap_or(tok.span.end);
                self.hir.insert_range(tok.span.extended(span_end).spanned(Range {
                    kind,
                    start: None,
                    end,
                }))
            }
            // `if` expression
            Token::Keyword(Keyword::If) => {
                self.lex.consume();
                let needs_parens = self.lex.nth(0).value == Token::BlockOpen(lex::Block::Brace);
                let cond = self.expr(ExprState {
                    parse_struct_value: false,
                    ..Default::default()
                })?;
                if needs_parens {
                    return self.error(self.hir.node_kind(cond).span,
                        "parentheses are required here".into());
                }
                let if_true = self.block()?;
                let if_false = if self.lex.maybe(Token::Keyword(Keyword::Else)).is_some() {
                    Some(if self.lex.nth(0).value == Token::Keyword(Keyword::If) {
                        self.expr(Default::default())?
                    } else {
                        self.block()?
                    })
                } else {
                    None
                };
                let end = self.hir.node_kind(if_false.unwrap_or(if_true)).span.end;
                self.hir.insert_if_expr(tok.span.extended(end).spanned(IfExpr {
                    cond,
                    if_true,
                    if_false,
                }))
            }
            Token::Keyword(Keyword::Let) => {
                if !state.at_group_start {
                    return self.error(tok.span, "this `let` usage requires explicit grouping".into());
                }
                let start = tok.span.start;
                self.lex.consume();
                let mut_ = self.lex.maybe(Token::Keyword(Keyword::Mut))
                    .map(|v| v.map(|_| {}));
                let name = self.ident()?;
                let ty = if self.lex.maybe(Token::Colon).is_some() {
                    Some(self.ty_expr()?)
                } else {
                    None
                };
                let init = if self.lex.maybe(Token::Eq).is_some() {
                    Some(self.expr(Default::default())?)
                } else {
                    None
                };
                let end = init.or(ty).map(|v| self.hir.node_kind(v).span.end)
                    .unwrap_or(name.span.end);
                let span = Span::new(start, end);
                let decl = self.hir.insert_let_decl(span.spanned(LetDecl {
                    mut_,
                    name,
                    ty,
                    init,
                }));
                self.hir.insert_let(span.spanned(Let {
                    decl,
                }))
            }
            // `while` expression
            Token::Keyword(Keyword::While) => {
                self.lex.consume();
                let needs_parens = self.lex.nth(0).value == Token::BlockOpen(lex::Block::Brace);
                let cond = self.expr(ExprState {
                    parse_struct_value: false,
                    ..Default::default()
                })?;
                if needs_parens {
                    return self.error(self.hir.node_kind(cond).span,
                        "parentheses are required here".into());
                }
                let block = self.block()?;
                self.hir.insert_while(tok.span.extended(self.hir.node_kind(block).span.end).spanned(While {
                    cond,
                    block,
                }))
            }
            // `loop` expression
            Token::Keyword(Keyword::Loop) => {
                self.lex.consume();
                let block = self.block()?;
                self.hir.insert_loop(tok.span.extended(self.hir.node_kind(block).span.end).spanned(Loop {
                    block,
                }))
            }
            _ => if let Some(v) = self.maybe_sym_path(false)? {
                v
            } else {
                return Ok(None);
            }
        };
        let left_is_block = matches!(tok.value, Token::BlockOpen(_));

        // Handle infix/postfix position.
        loop {
            let tok = self.lex.nth(0);
            let PrecAssoc { prec, assoc } = match tok.value {
                // Named struct value.
                Token::BlockOpen(lex::Block::Brace)
                    if state.parse_struct_value
                        && self.hir.node_kind(left).value == NodeKind::Path
                => {
                    NAMED_STRUCT_VALUE_PREC
                }

                // Field access or method call
                Token::Dot => FIELD_ACCESS_PREC,

                // Free fn call
                | Token::BlockOpen(lex::Block::Paren)
                // Indexing
                | Token::BlockOpen(lex::Block::Bracket)
                => FN_CALL_PREC,

                Token::Quest | Token::Excl => UNWRAP_PREC,

                Token::Keyword(Keyword::As) => AS_PREC,
                Token::Star | Token::Slash | Token::Percent => MUL_PREC,
                Token::Plus | Token::Minus => PLUS_PREC,
                Token::GtGt | Token::LtLt => SHIFT_PREC,
                Token::Amp => BIT_AND_PREC,
                Token::Hat => BIT_XOR_PREC,
                Token::Pipe => BIT_OR_PREC,

                | Token::EqEq
                | Token::ExclEq
                | Token::Lt
                | Token::LtEq
                | Token::Gt
                | Token::GtEq
                => {
                    if !left_is_block {
                        self.check_assoc_defined(left, tok,
                            |k| matches!(k,
                                BinaryOpKind::Eq
                                | BinaryOpKind::NotEq
                                | BinaryOpKind::Lt
                                | BinaryOpKind::LtEq
                                | BinaryOpKind::Gt
                                | BinaryOpKind::GtEq))?;
                    }
                    CMP_PREC
                }

                Token::AmpAmp => AND_PREC,
                Token::PipePipe => OR_PREC,
                Token::DotDot | Token::DotDotEq => {
                    if !left_is_block {
                        self.check_assoc_defined(left, tok,
                            |k| matches!(k, BinaryOpKind::RangeExcl | BinaryOpKind::RangeIncl))?;
                    }
                    RANGE_PREC
                }

                | Token::Eq
                | Token::PlusEq
                | Token::MinusEq
                | Token::StarEq
                | Token::SlashEq
                | Token::PercentEq
                | Token::GtGtEq
                | Token::LtLtEq
                | Token::HatEq
                | Token::PipeEq
                | Token::AmpEq
                => {
                    if !state.at_group_start {
                        let start = self.hir.node_kind(left).span.start;
                        return self.error(Span::new(start, tok.span.end),
                            "this assignment operator usage requires parentheses".into());
                    }
                    ASSIGN_PREC
                },

                _ => break,
            };

            if prec < state.min_prec {
                break;
            }
            let state = state.with_min_prec(prec + assoc);

            self.lex.consume();

            let simple = match tok.value {
                Token::Star => Some(BinaryOpKind::Mul),
                Token::Slash => Some(BinaryOpKind::Div),
                Token::Percent => Some(BinaryOpKind::Rem),
                Token::Plus => Some(BinaryOpKind::Add),
                Token::Minus => Some(BinaryOpKind::Sub),
                Token::GtGt => Some(BinaryOpKind::Shr),
                Token::LtLt => Some(BinaryOpKind::Shl),
                Token::Amp => Some(BinaryOpKind::BitAnd),
                Token::Hat => Some(BinaryOpKind::BitXor),
                Token::Pipe => Some(BinaryOpKind::BitOr),
                Token::EqEq => Some(BinaryOpKind::Eq),
                Token::ExclEq => Some(BinaryOpKind::NotEq),
                Token::Lt => Some(BinaryOpKind::Lt),
                Token::LtEq => Some(BinaryOpKind::LtEq),
                Token::Gt => Some(BinaryOpKind::Gt),
                Token::GtEq => Some(BinaryOpKind::GtEq),
                Token::AmpAmp => Some(BinaryOpKind::And),
                Token::PipePipe => Some(BinaryOpKind::Or),
                Token::Eq => Some(BinaryOpKind::Assign),
                Token::PlusEq => Some(BinaryOpKind::AddAssign),
                Token::MinusEq => Some(BinaryOpKind::SubAssign),
                Token::StarEq => Some(BinaryOpKind::MulAssign),
                Token::SlashEq => Some(BinaryOpKind::DivAssign),
                Token::PercentEq => Some(BinaryOpKind::RemAssign),
                Token::GtGtEq => Some(BinaryOpKind::ShrAssign),
                Token::LtLtEq => Some(BinaryOpKind::ShlAssign),
                Token::HatEq => Some(BinaryOpKind::BitXorAssign),
                Token::PipeEq => Some(BinaryOpKind::BitOrAssign),
                Token::AmpEq => Some(BinaryOpKind::BitAndAssign),
                _ => None,
            };
            left = if let Some(simple) = simple {
                self.binary_op(tok.span, left, simple, state)?
            } else {
                match tok.value {
                    // Named struct value.
                    Token::BlockOpen(lex::Block::Brace)
                        if self.hir.node_kind(left).value == NodeKind::Path =>
                    {
                        self.block_or_struct(Some(left), self.hir.node_kind(left).span.start)?
                    }

                    Token::Dot => {
                        self.field_access_or_method_call(left)?
                    }
                    // Free fn call
                    Token::BlockOpen(lex::Block::Paren) => {
                        self.fn_call(left, None)?
                    }
                    // Indexing
                    Token::BlockOpen(lex::Block::Bracket) => {
                        let r = self.binary_op(tok.span, left, BinaryOpKind::Index,
                            Default::default())?;
                        self.expect(Token::BlockClose(lex::Block::Bracket))?;
                        r
                    }
                    Token::Quest => {
                        self.hir.insert_op(self.hir.node_kind(left).span.extended(tok.span.end).spanned(
                            Op::Unary(UnaryOp {
                                kind: tok.span.spanned(UnaryOpKind::PropagatingUnwrap),
                                arg: left,
                            })))
                    }
                    Token::Excl => {
                        self.hir.insert_op(self.hir.node_kind(left).span.extended(tok.span.end).spanned(
                            Op::Unary(UnaryOp {
                                kind: tok.span.spanned(UnaryOpKind::PanickingUnwrap),
                                arg: left,
                            })))
                    }
                    Token::Keyword(Keyword::As) => {
                        let ty = self.ty_expr()?;
                        let span = self.hir.node_kind(left).span
                            .extended(self.hir.node_kind(ty).span.end);
                        self.hir.insert_cast(span.spanned(
                            Cast {
                                expr: left,
                                ty,
                            }))
                    }
                    // Start-bounded range
                    Token::DotDot | Token::DotDotEq => {
                        let kind = if tok.value == Token::DotDot {
                            RangeKind::Exclusive
                        } else {
                            RangeKind::Inclusive
                        };
                        let end = self.maybe_expr(Default::default())?;
                        let span_end = end.map(|v| self.hir.node_kind(v).span.end)
                            .unwrap_or(tok.span.end);
                        self.hir.insert_range(tok.span.extended(span_end).spanned(Range {
                            kind,
                            start: Some(left),
                            end,
                        }))
                    }
                    _ => unreachable!(),
                }
            }
        }
        Ok(Some(left))
    }

    fn field_access_or_method_call(&mut self, receiver: NodeId) -> PResult<NodeId> {
        let field = self.lex.nth(0);
        let field = match field.value {
            Token::Ident => {
                let ident = self.ident()?;
                if self.lex.maybe(Token::BlockOpen(lex::Block::Paren)).is_some() {
                    let callee = self.hir.insert_path_from_ident(ident);
                    return self.fn_call(callee, Some(receiver));
                }
                ident.map(Field::Ident)
            }
            Token::Literal(lex::Literal::Int) => {
                let IntLiteral { value, ty } = self.int_literal()?.value;
                if ty.is_some() {
                    return self.error(field.span,
                        "type suffix is not allowed in tuple field index".into());
                }
                let idx = if let Ok(v) = i32::try_from(value) {
                    v as u32
                } else {
                    return self.error(field.span, "tuple field index is too big".into());
                };
                field.span.spanned(Field::Index(idx))
            }
            _ => {
                return self.error(field.span,
                    format!("expected field identifier or tuple field index, found `{}`", field.value));
            }
        };
        let span = self.hir.node_kind(receiver).span.extended(field.span.end);
        Ok(self.hir.insert_field_access(span.spanned(
            FieldAccess {
                receiver,
                field,
            })))
    }

    // Expects the opening paren to be already consumed.
    fn fn_call(&mut self, callee: NodeId, receiver: Option<NodeId>) -> PResult<NodeId> {
        let mut args = Vec::new();
        let kind = if let Some(receiver) = receiver {
            args.push(FnCallArg {
                name: None,
                value: receiver,
            });
            FnCallKind::Method
        } else {
            FnCallKind::Free
        };
        let end = loop {
            let name = if self.lex.nth(0).value == Token::Ident
                && self.lex.nth(1).value == Token::Colon
            {
                let name = self.ident().unwrap();
                self.expect(Token::Colon).unwrap();
                Some(name)
            } else {
                None
            };
            let value = self.maybe_expr(ExprState {
                at_group_start: true,
                ..Default::default()
            })?;
            if let Some(value) = value {
                args.push(FnCallArg {
                    name,
                    value,
                });

                let tok = self.lex.next();
                match tok.value {
                    Token::Comma => {},
                    Token::BlockClose(lex::Block::Paren) => break tok.span.end,
                    _ => return self.error(tok.span,
                        format!("expected `,` or `)`, found `{}`", tok.value)),
                }
            } else {
                if name.is_some() {
                    let tok = self.lex.nth(0);
                    return self.error(tok.span,
                        format!("expected expression, found `{}`", tok.value));
                }
                let tok = self.expect(Token::BlockClose(lex::Block::Paren))?;
                break tok.span.end;
            }
        };
        let span = self.hir.node_kind(callee).span.extended(end);
        Ok(self.hir.insert_fn_call(span.spanned(FnCall {
            callee,
            kind,
            args,
        })))
    }

    fn literal(&mut self) -> PResult<NodeId> {
        let tok = self.lex.nth(0);
        let kind = if let Token::Literal(v) = tok.value {
            v
        } else {
            return self.error(tok.span, format!("expected literal, found `{}`", tok.value))?;
        };
        let lit = match kind {
            lex::Literal::Int => {
                Literal::Int(self.int_literal()?.value)
            }
            lex::Literal::String => {
                self.lex.consume();
                self.string_literal(tok.span)?
            }
            lex::Literal::Float => {
                self.lex.consume();
                self.float_literal(tok.span)?
            }
            lex::Literal::Char => {
                self.lex.consume();
                self.char_literal(tok.span)?
            }
        };
        Ok(self.hir.insert_literal(tok.with_value(lit)))
    }

    fn int_literal(&mut self) -> PResult<S<IntLiteral>> {
        let span = self.expect(Token::Literal(lex::Literal::Int))?.span;
        let s = &self.s[span.range()];
        match s.parse::<IntLiteral>() {
            Ok(v) => Ok(span.spanned(v)),
            Err(_) => {
                self.error(span, "invalid integer literal".into())
            }
        }
    }

    fn float_literal(&mut self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        match s.parse::<FloatLiteral>() {
            Ok(v) => Ok(Literal::Float(v)),
            Err(_) => {
                self.error(span, "invalid floating point literal".into())
            }
        }
    }

    fn string_literal(&mut self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        match lex::string_literal(s) {
            Ok(s) => Ok(Literal::String(s)),
            Err(lex::StringLiteralError) => {
                self.error(span, "invalid string literal".into())
            }
        }
    }

    fn char_literal(&mut self, span: Span) -> PResult<Literal> {
        let s = &self.s[span.range()];
        match lex::char_literal(s) {
            Ok(s) => Ok(Literal::Char(s)),
            Err(lex::CharLiteralError) => {
                self.error(span, "invalid char literal".into())
            }
        }
    }

    fn struct_(&mut self, vis: Option<S<Vis>>) -> PResult<NodeId> {
        self.expect(Token::Keyword(Keyword::Struct))?;

        let name = self.ident()?;
        let ty_args = self.maybe_formal_ty_args()?;
        let ty = self.struct_type(true)?;

        let start = vis.as_ref().map(|v| v.span.start)
            .unwrap_or(name.span.start);
        let end = self.hir.node_kind(ty).span.end;
        Ok(self.hir.insert_struct(Span::new(start, end).spanned(Struct {
            vis,
            name,
            ty_args,
            ty,
        })))
    }

    fn impl_(&mut self) -> PResult<NodeId> {
        let start = self.expect(Token::Keyword(Keyword::Impl))?.span.start;
        let ty_args = self.maybe_formal_ty_args()?;
        let sym1 = self.sym_path(true)?;
        let sym2 = if self.lex.maybe(Token::Keyword(Keyword::For)).is_some() {
            Some(self.sym_path(true)?)
        } else {
            None
        };
        let (trait_, for_) = if let Some(sym2) = sym2 {
            (Some(sym1), sym2)
        } else {
            (None, sym1)
        };

        if self.lex.maybe(Token::BlockOpen(lex::Block::Brace)).is_none() {
            let tok = self.lex.nth(0);
            return self.error(tok.span,
                format!("expected `for` or `{{`, found `{}`", tok.value));
        }

        let mut items = Vec::new();
        while self.lex.nth(0).value != Token::BlockClose(lex::Block::Brace) {
            let vis = self.maybe_vis();
            let fn_ = self.fn_(vis)?;
            items.push(fn_);
        }

        let end = self.expect(Token::BlockClose(lex::Block::Brace)).unwrap()
            .span.end;

        Ok(self.hir.insert_impl(Span::new(start, end).spanned(Impl {
            ty_args,
            trait_,
            for_,
            items,
        })))
    }

    fn struct_type(&mut self, field_vis: bool) -> PResult<NodeId> {
        let start = self.expect(Token::BlockOpen(lex::Block::Brace))?.span.start;
        let mut fields = Vec::new();
        let mut delimited = true;
        let mut named_fields = false;
        while self.lex.nth(0).value != Token::BlockClose(lex::Block::Brace) {
            if !delimited {
                let tok = self.lex.nth(0);
                return self.error(tok.span, format!("expected `,` or `}}` but found `{}`", tok.value));
            }
            let vis = if field_vis {
                self.maybe_vis()
            } else {
                None
            };
            named_fields = named_fields ||
                self.lex.nth(0).value == Token::Ident && self.lex.nth(1).value == Token::Colon;
            let name = if named_fields {
                let name = self.ident()?;
                self.expect(Token::Colon)?;
                Some(name)
            } else {
                None
            };
            let ty = self.ty_expr()?;
            fields.push(StructTypeField {
                vis,
                name,
                ty,
            });
            delimited = self.lex.maybe(Token::Comma).is_some();
        }
        let end = self.expect(Token::BlockClose(lex::Block::Brace)).unwrap().span;

        if !named_fields && !delimited && fields.len() == 1 {
            return self.error(end, "expected `,`".into());
        }

        Ok(self.hir.insert_struct_type(Span::new(start, end.end).spanned(StructType {
            fields,
        })))
    }

    // Expects the first '{' be already consumed.
    fn block_or_struct(&mut self, struct_name: Option<NodeId>, start: usize) -> PResult<NodeId> {
        enum Probe {
            StructStart {
                first_field: S<StructValueField>,
                explicit_tuple: Option<S<()>>,
            },
            EmptyStruct {
                end: usize,
            },
            Block,
        }
        // If there's a name it's always a struct, never a block.
        let is_struct = struct_name.is_some();
        let probe = if self.lex.nth(0).value == Token::Ident && self.lex.nth(1).value == Token::Colon {
            let name = self.ident()?;
            self.expect(Token::Colon).unwrap();
            let value = self.expr(Default::default())?;
            Probe::StructStart {
                first_field: Span::new(name.span.start, self.hir.node_kind(value).span.end).spanned(StructValueField {
                    name: Some(name),
                    value,
                }),
                explicit_tuple: None,
            }
        } else if self.lex.nth(0).value == Token::Literal(lex::Literal::Int)
            && self.lex.nth(1).value == Token::Colon
        {
            let explicit_tuple = self.int_literal()?;
            if explicit_tuple.value.ty.is_some() {
                return self.error(explicit_tuple.span, "unexpected int literal type suffix".into());
            }
            if explicit_tuple.value.value != 0 {
                return self.error(explicit_tuple.span, "invalid tuple field number".into());
            }
            self.expect(Token::Colon).unwrap();
            let value = self.expr(Default::default())?;
            Probe::StructStart {
                first_field: self.hir.node_kind(value).span.spanned(StructValueField {
                    name: None,
                    value,
                }),
                explicit_tuple: Some(explicit_tuple.with_value({})),
            }
        } else if is_struct && self.lex.nth(0).value == Token::BlockClose(lex::Block::Brace) {
            let end = self.expect(Token::BlockClose(lex::Block::Brace)).unwrap().span.end;
            Probe::EmptyStruct { end }
        } else {
            let save = if is_struct { None } else { Some(self.save_state()) };
            match self.expr(Default::default()) {
                Ok(value) if is_struct || self.lex.nth(0).value == Token::Comma => {
                    if let Some(save) = save {
                        self.discard_state(save);
                    }
                    Probe::StructStart {
                        first_field: self.hir.node_kind(value).span.spanned(StructValueField {
                            name: None,
                            value,
                        }),
                        explicit_tuple: None,
                    }
                }
                Err(err) if is_struct => {
                    return Err(err);
                }
                _ => {
                    assert!(!is_struct);
                    if let Some(save) = save {
                        // FIXME remove added HIR nodes
                        self.restore_state(save);
                    }
                    Probe::Block
                }
            }
        };
        Ok(match probe {
            Probe::StructStart { first_field , explicit_tuple } => {
                let mut fields = Vec::new();
                fields.push(self.hir.insert_struct_value_field(first_field));
                loop {
                    let delimited = self.lex.maybe(Token::Comma).is_some();
                    if self.lex.nth(0).value == Token::BlockClose(lex::Block::Brace) {
                        break;
                    }
                    if !delimited {
                        let tok = self.lex.nth(0);
                        return self.error(tok.span, format!("expected `,` or `}}` but found `{}`", tok.value));
                    }

                    let name = if self.lex.nth(0).value == Token::Ident
                        && self.lex.nth(1).value == Token::Colon
                    {
                        if explicit_tuple.is_some() {
                            let tok = self.lex.nth(0);
                            return self.error(tok.span, "unexpected field name".into());
                        }
                        let name = self.ident()?;
                        self.expect(Token::Colon)?;
                        Some(name)
                    } else {
                        None
                    };

                    let value = self.expr(Default::default())?;

                    let value_span = self.hir.node_kind(value).span;
                    let start = name.as_ref().map(|v| v.span.start).unwrap_or(value_span.start);
                    fields.push(self.hir.insert_struct_value_field(Span::new(start, value_span.end).spanned(
                        StructValueField {
                            name,
                            value,
                        })));
                }
                let end = self.expect(Token::BlockClose(lex::Block::Brace)).unwrap().span.end;

                self.hir.insert_struct_value(Span::new(start, end).spanned(StructValue {
                    name: struct_name,
                    explicit_tuple,
                    fields,
                }))
            }
            Probe::EmptyStruct { end } => {
                self.hir.insert_struct_value(Span::new(start, end).spanned(StructValue {
                    name: struct_name,
                    explicit_tuple: None,
                    fields: Vec::new(),
                }))
            }
            Probe::Block => {
                self.block_inner(start)?
            }
        })
    }

    fn save_state(&mut self) -> SaveState {
        let lex = self.lex.save_state();
        let diag = self.diag.save_state();
        SaveState {
            lex,
            diag,
        }
    }

    fn restore_state(&mut self, state: SaveState) {
        self.lex.restore_state(state.lex);
        self.diag.restore_state(state.diag);
    }

    fn discard_state(&mut self, state: SaveState) {
        self.lex.discard_state(state.lex);
    }
}

struct SaveState {
    lex: lex::SavedStateId,
    diag: diag::SaveState,
}

fn read_file(fs: &mut dyn Fs, path: &StdPath) -> PResult<String> {
    fs.read_file(path).map_err(|e| ErrorKind::Io(e).into())
}

pub struct Error {
    pub kind: ErrorKind,
    pub sources: Sources,
    pub backtrace: Option<Box<backtrace::Backtrace>>,
}

impl Error {
    fn from_perror(PError { kind, backtrace }: PError, hir: Hir) -> Self {
        Self {
            kind,
            sources: hir.into_sources(),
            backtrace,
        }
    }
}

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.kind {
            ErrorKind::Io(e) => write!(f, "Parser error ({:?})", e),
            ErrorKind::Lex => write!(f, "Parser error (lexer)"),
            ErrorKind::Parse => write!(f, "Parser error"),
        }?;
        if let Some(backtrace) = &self.backtrace {
            writeln!(f)?;
            write!(f, "{:?}", backtrace)?;
        }
        Ok(())
    }
}

pub fn parse_file_with(path: impl AsRef<StdPath>, fs: &mut dyn Fs, diag: &mut Diag) -> std::result::Result<Hir, Error> {
    let path = path.as_ref().to_path_buf();
    let hir = Hir::new();
    let text = match read_file(fs, &path) {
        Ok(v) => v,
        Err(e) => return Err(Error::from_perror(e, hir)),
    };
    parse(path, text, hir, fs, diag)
}

pub fn parse_file(path: impl AsRef<StdPath>, diag: &mut Diag) -> std::result::Result<Hir, Error> {
    struct StdFs;
    impl Fs for StdFs {
        fn read_file(&mut self, path: &StdPath) -> io::Result<String> {
            std::fs::read_to_string(path)
        }
    }
    parse_file_with(path, &mut StdFs, diag)
}

pub fn parse_str(text: String, diag: &mut Diag) -> std::result::Result<Hir, Error> {
    struct NotFoundFs;
    impl Fs for NotFoundFs {
        fn read_file(&mut self, _path: &StdPath) -> io::Result<String> {
            Err(io::Error::new(io::ErrorKind::NotFound, "not found"))
        }
    }

    let path = source_file_name("unnamed");
    parse(path, text, Hir::new(), &mut NotFoundFs, diag)
}

fn parse(path: PathBuf, text: String, mut hir: Hir, fs: &mut dyn Fs, diag: &mut Diag) -> std::result::Result<Hir, Error> {
    let text = Arc::new(text);
    let source_id = hir.sources_mut().insert(Source {
        mod_name: None,
        text: text.clone(),
        path,
    });
    match ParserImpl::new(&text, source_id, fs, &mut hir, diag).parse(){
        Ok(()) => Ok(hir),
        Err(e) => Err(Error::from_perror(e, hir)),
    }
}

pub fn needs_trailing_semi(kind: NodeKind) -> bool {
    use NodeKind::*;
    match kind {
        | Block
        | Impl
        | IfExpr
        | Loop
        | FnDecl
        | Module
        | Struct
        | StructType
        // `;` is the part of the `use` itself.
        | Use
        | While
        => false,

        | BlockFlowCtl
        | Cast
        | FieldAccess
        | FnCall
        | FnDeclArg
        | Let
        | LetDecl
        | Literal
        | Op
        | Path
        | PathSegment
        | PathEndEmpty
        | PathEndIdent
        | PathEndStar
        | Range
        | TyExpr
        | TypeArg
        | StructValue
        | StructValueField
        => true,
    }
}