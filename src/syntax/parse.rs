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

const NAMED_STRUCT_LITERAL_PREC: PrecAssoc = PrecAssoc { prec: 10000, assoc: 1 };
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

#[derive(Clone, Copy, Default)]
struct ExprState {
    min_prec: u32,

    /// Disables struct literals parsing. This is needed within conditions of `if` and `while`.
    disable_struct_literal: bool,

    /// Are we immediately after '{' or '('?
    at_block_start: Option<lex::Block>,
}

impl ExprState {
    fn block_start(block: lex::Block) -> Self {
        Self {
            at_block_start: Some(block),
            ..Default::default()
        }
    }

    fn disable_struct_literal() -> Self {
        Self {
            disable_struct_literal: true,
            ..Default::default()
        }
    }

    fn operand(self, min_prec: u32) -> Self {
        Self {
            min_prec,
            disable_struct_literal: self.disable_struct_literal,
            ..Default::default()
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
            Token::Keyword(Keyword::Module) => self.module(top_level, vis)?,
            Token::Keyword(Keyword::Static) => unimplemented!(),
            Token::Keyword(Keyword::Use) => self.use_(vis)?,
            Token::Keyword(Keyword::Struct) => self.struct_(vis)?,
            Token::Keyword(Keyword::Type) => self.type_alias(vis)?,
            Token::Keyword(Keyword::Impl) => {
                if let Some(vis) = vis {
                    return self.error(vis.span, "invalid visibility for impl block".into())
                }
                self.impl_()?
            }
            _ => {
                if vis.is_some() {
                    return self.error(tok0.span,
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
        let module = self.expect(Token::Keyword(Keyword::Module))?;
        let start = vis.as_ref().map(|v| v.span.start)
            .unwrap_or(module.span.start);
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
        let path_start = anchor.as_ref().map(|v| v.span.start)
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
        let ty_params = self.maybe_ty_params()?;

        let mut params = Vec::new();
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
                let param = if params.is_empty() {
                    let ref_ = self.lex.maybe(Token::Amp);
                    let mut_ = self.lex.maybe(Token::Keyword(Keyword::Mut));
                    let self_ = self.lex.maybe(Token::Keyword(Keyword::SelfLower));
                    if (ref_.is_some() || mut_.is_some()) && self_.is_none() {
                        let tok = self.lex.nth(0);
                        return self.error(tok.span, format!("expected `self`, found `{}`", tok.value));
                    }
                    if let Some(self_) = self_ {
                        let ty = self.hir.insert_path_from_ident(self_.with_value(Ident::self_upper()), None);
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
                        let name = self_.with_value(Ident::self_lower());
                        Some(FnDefParam {
                            label: name.clone().map(Some),
                            name,
                            ty,
                        })
                    } else {
                        None
                    }
                } else {
                    None
                };
                let param = if let Some(param) = param {
                    param
                } else {
                    let (label, name) = if let Some(underscore) = self.lex.maybe(Token::Keyword(Keyword::Underscore)) {
                        let name = self.ident()?;
                        (underscore.with_value(None), name)
                    } else {
                        let label = self.ident()?;
                        let name = self.maybe_ident()?.unwrap_or_else(|| label.clone());
                        (label.map(Some), name)
                    };
                    self.expect(Token::Colon)?;
                    let ty = self.ty_expr()?;
                    FnDefParam { label, name, ty }
                };
                let start = param.label.span.start;
                let end = self.hir.node_kind(param.ty).span.end;
                params.push(self.hir.insert_fn_def_param(Span::new(start, end).spanned(param)));
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
        Ok(self.hir.insert_fn_def(span.spanned(FnDef {
            name,
            vis,
            ty_params,
            params,
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
        self.make_ident(tok.span, lex::IdentContext::Other)
    }

    fn maybe_ident(&mut self) -> PResult<Option<S<Ident>>> {
        Ok(if let Some(tok) = self.lex.maybe(Token::Ident) {
            Some(self.make_ident(tok.span, lex::IdentContext::Other)?)
        } else {
            None
        })
    }

    fn make_ident(&mut self, span: Span, ctx: lex::IdentContext) -> PResult<S<Ident>> {
        let s = &self.s[span.range()];
        let value = lex::ident(s, ctx);
        if value.is_empty() {
            self.error(span, "missing raw identifier or raw string".into())
        } else {
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
            Token::BlockOpen(lex::Block::Bracket) => {
                self.lex.consume();
                let item = self.ty_expr()?;
                let len = if self.lex.maybe(Token::Semi).is_some() {
                    Some(self.expr(Default::default())?)
                } else {
                    None
                };
                let end = self.expect(Token::BlockClose(lex::Block::Bracket))?.span.end;
                (end, TyData::Slice(SliceType {
                    item_ty: item,
                    len,
                }))
            }
            Token::BlockOpen(lex::Block::Brace) => {
                let struct_ = self.struct_type(false, false)?;
                (self.hir.node_kind(struct_).span.end, TyData::Struct(struct_))
            }
            _ => {
                let path = self.path(true)?;
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
                    PathAnchor::Package { name: None }
                }
                Token::Keyword(Keyword::Package) => {
                    self.lex.consume();
                    self.expect(Token::BlockOpen(lex::Block::Paren))?;
                    let name = self.ident()?;
                    self.expect(Token::BlockClose(lex::Block::Paren))?;
                    PathAnchor::Package { name: Some(name) }
                }
                _ => return Ok(None),
            })
        };
        if !matches!(r.value, PathAnchor::Package { name: None }) {
            self.expect(Token::ColonColon)?;
        }
        Ok(Some(r))
    }

    fn path(&mut self, in_type_pos: bool) -> PResult<NodeId> {
        if let Some(v) = self.maybe_path(in_type_pos)? {
            Ok(v)
        } else {
            let tok = self.lex.nth(0);
            return self.error(tok.span, format!("expected symbol path, found `{}`", tok.value));
        }
    }

    fn maybe_path(&mut self, in_type_pos: bool) -> PResult<Option<NodeId>> {
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

            let (ty_args, done) = self.maybe_ty_args(in_type_pos)?;

            items.push(PathItem {
                ident,
                ty_args,
            });

            if done || self.lex.maybe(Token::ColonColon).is_none() {
                break;
            }
        }

        Ok(Some(self.hir.insert_path_from_items(anchor, items)))
    }

    fn maybe_ty_args(&mut self, in_type_pos: bool) -> PResult<(Option<S<Vec<NodeId>>>, bool)> {
        if self.lex.nth(0).value != Token::Lt {
            return Ok((None, false));
        }
        // FIXME remove added HIR nodes when restoring state
        let save = self.save_state();
        Ok(match self.path_ty_args() {
            Ok(ty_args) => {
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
                            (Some(ty_args), false)
                        }
                        _ => {
                            self.restore_state(save);
                            (None, true)
                        }
                    }
                } else {
                    self.discard_state(save);
                    (Some(ty_args), false)
                }
            }
            Err(e) => {
                if in_type_pos {
                    self.discard_state(save);
                    return Err(e);
                }
                self.restore_state(save);
                (None, true)
            }
        })
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
                    ty_args: None,
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
                let tok = self.lex.nth(0);
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
                            ty_args: None,
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

    fn path_ty_args(&mut self) -> PResult<S<Vec<NodeId>>> {
        let start = self.expect(Token::Lt)?.span.start;
        let mut ty_params = Vec::new();
        let end = loop {
            if !matches!(self.lex.nth(0).value, Token::Gt | Token::GtGt) {
                ty_params.push(self.ty_expr()?);
            }
            let mut tok = self.lex.nth(0);
            // Split GtGt into Gt and Gt.
            if tok.value == Token::GtGt {
                self.lex.consume();
                let i = tok.span.start;
                self.lex.insert(Span::new(i + 1, i + 2).spanned(Token::Gt));
                self.lex.insert(Span::new(i, i + 1).spanned(Token::Gt));

                tok = self.lex.nth(0);
            }
            self.lex.consume();
            match tok.value {
                Token::Comma => {}
                Token::Gt => {
                    break tok.span.end;
                }
                _ => {
                    return self.error(tok.span,
                        format!("expected `,` or `>`, found `{}`", tok.value));
                }
            }
        };
        Ok(Span::new(start, end).spanned(ty_params))
    }

    fn maybe_ty_params(&mut self) -> PResult<Vec<NodeId>> {
        let tok = self.lex.nth(0);
        if tok.value != Token::Lt {
            return Ok(Vec::new());
        }

        let mut ty_params = Vec::new();

        self.lex.consume();

        loop {
            let name = self.ident()?;
            ty_params.push(self.hir.insert_type_param(name.span.spanned(TypeParam {
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
        Ok(ty_params)
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
                self.maybe_expr(ExprState::block_start(lex::Block::Brace))?
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
                    exprs.push(self.hir.insert_struct_literal(semi.span.spanned(StructLiteral {
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
        let arg = self.expr(state.operand(UNARY_PREC.prec))?;
        Ok(self.hir.insert_op(Span::new(span.start, self.hir.node_kind(arg).span.end).spanned(
            Op::Unary(UnaryOp {
                kind: span.spanned(kind),
                arg,
            }))))
    }

    fn binary_op(&mut self,
        mut span: Span,
        left: NodeId,
        kind: BinaryOpKind,
        state: ExprState,
    ) -> PResult<NodeId> {
        let right = self.expr(state)?;
        let start = self.hir.node_kind(left).span.start;
        let end = if kind == BinaryOpKind::Index {
            let end = self.expect(Token::BlockClose(lex::Block::Bracket))?.span.end;
            span.end = end;
            end
        } else {
            self.hir.node_kind(right).span.end
        };
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
                self.hir.insert_ctl_flow_abort(tok.span.extended(span_end).spanned(CtlFlowAbort {
                    kind: CtlFlowAbortKind::Break,
                    label,
                    value,
                }))
            }
            Token::Keyword(Keyword::Continue) => {
                self.lex.consume();
               self.hir.insert_ctl_flow_abort(tok.span.spanned(CtlFlowAbort {
                    kind: CtlFlowAbortKind::Continue,
                    label: None,
                    value: None,
                }))
            }
            Token::Keyword(Keyword::Return) => {
                self.lex.consume();
                let value = self.maybe_expr(Default::default())?;
                let span_end = value.map(|v| self.hir.node_kind(v).span.end)
                    .unwrap_or(tok.span.end);

                self.hir.insert_ctl_flow_abort(tok.span.extended(span_end).spanned(CtlFlowAbort {
                    kind: CtlFlowAbortKind::Return,
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

                let expr = self.expr(ExprState::block_start(lex::Block::Paren))?;
                self.expect(Token::BlockClose(lex::Block::Paren))?;
                expr
            }
            // Block or unnamed struct
            Token::BlockOpen(lex::Block::Brace) => {
                self.lex.consume();
                self.block_or_struct_literal(None, tok.span.start)?
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
                let cond = self.expr(ExprState::disable_struct_literal())?;
                let if_true = self.block()?;
                let if_false = if self.lex.maybe(Token::Keyword(Keyword::Else)).is_some() {
                    Some(if self.lex.nth(0).value == Token::Keyword(Keyword::If) {
                        self.expr(ExprState::block_start(lex::Block::Brace))?
                    } else {
                        self.block()?
                    })
                } else {
                    None
                };
                let end = self.hir.node_kind(if_false.unwrap_or(if_true)).span.end;
                let node = self.hir.insert_if_expr(tok.span.extended(end).spanned(IfExpr {
                    cond,
                    if_true,
                    if_false,
                }));
                if state.at_block_start == Some(lex::Block::Brace) {
                    return Ok(Some(node));
                }
                node
            }
            Token::Keyword(Keyword::Let) => {
                if state.at_block_start.is_none() {
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
                let def = self.hir.insert_let_def(span.spanned(LetDef {
                    mut_,
                    name,
                    ty,
                    init,
                }));
                self.hir.insert_let(span.spanned(Let {
                    def,
                }))
            }
            // `while` expression
            Token::Keyword(Keyword::While) => {
                self.lex.consume();
                let cond = self.expr(ExprState::disable_struct_literal())?;
                let body = self.block()?;
                self.hir.insert_while(tok.span.extended(self.hir.node_kind(body).span.end).spanned(While {
                    cond,
                    body,
                }))
            }
            // `loop` expression
            Token::Keyword(Keyword::Loop) => {
                self.lex.consume();
                let body = self.block()?;
                self.hir.insert_loop(tok.span.extended(self.hir.node_kind(body).span.end).spanned(Loop {
                    body,
                }))
            }
            // Slice literal:
            // []
            // [1, 2, 3]
            // [{ let x = 42; x },]
            // [42; 100]
            // [=]
            // [=1,2,3]
            | Token::BlockOpen(lex::Block::Bracket)
            | Token::BlockOpen(lex::Block::BracketEq)
            => {
                let const_len = tok.value == Token::BlockOpen(lex::Block::BracketEq);
                let start = tok.span.start;
                self.lex.consume();
                let mut items = Vec::new();
                let first = self.maybe_expr(Default::default())?;
                let len;
                if let Some(first) = first {
                    items.push(first);
                    if self.lex.maybe(Token::Semi).is_some() {
                        len = Some(self.expr(Default::default())?);
                    } else {
                        len = None;
                        self.lex.maybe(Token::Comma);
                        loop {
                            let item = if let Some(v) = self.maybe_expr(Default::default())? {
                                v
                            } else {
                                break;
                            };
                            items.push(item);
                            self.lex.maybe(Token::Comma);
                        }
                    }
                } else {
                    len = None
                };
                let end = self.expect(Token::BlockClose(lex::Block::Bracket))?.span.end;
                self.hir.insert_slice_literal(Span::new(start, end).spanned(SliceLiteral {
                    items,
                    len: SliceLiteralLen {
                        value: len,
                        const_: const_len,
                    },
                }))
            }
            // [=42; 100]
            _ => if let Some(v) = self.maybe_path(false)? {
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
                    if !state.disable_struct_literal
                        && self.hir.node_kind(left).value == NodeKind::Path
                => {
                    NAMED_STRUCT_LITERAL_PREC
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
                    ASSIGN_PREC
                },

                _ => break,
            };

            if prec < state.min_prec {
                break;
            }
            let state = state.operand(prec + assoc);

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
                    // Named struct literal.
                    Token::BlockOpen(lex::Block::Brace)
                        if self.hir.node_kind(left).value == NodeKind::Path =>
                    {
                        self.block_or_struct_literal(Some(left), self.hir.node_kind(left).span.start)?
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
                        self.binary_op(tok.span, left, BinaryOpKind::Index, Default::default())?
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
                        self.hir.insert_range(self.hir.node_kind(left).span.extended(span_end).spanned(Range {
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
        let name = match field.value {
            Token::Ident => {
                let ident = self.ident()?;
                let (ty_args, _) = self.maybe_ty_args(false)?;
                if self.lex.maybe(Token::BlockOpen(lex::Block::Paren)).is_some() {
                    let callee = self.hir.insert_path_from_ident(ident, ty_args);
                    return self.fn_call(callee, Some(receiver));
                }
                ident.map(FieldAccessName::Ident)
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
                field.span.spanned(FieldAccessName::Index(idx))
            }
            _ => {
                return self.error(field.span,
                    format!("expected field identifier or tuple field index, found `{}`", field.value));
            }
        };
        let span = self.hir.node_kind(receiver).span.extended(name.span.end);
        Ok(self.hir.insert_field_access(span.spanned(
            FieldAccess {
                receiver,
                name,
            })))
    }

    // Expects the opening paren to be already consumed.
    fn fn_call(&mut self, callee: NodeId, receiver: Option<NodeId>) -> PResult<NodeId> {
        let mut args = Vec::new();
        let kind = if let Some(receiver) = receiver {
            args.push(FnCallArg {
                name: Some(self.hir.node_kind(receiver).span.spanned(Ident::self_lower())),
                value: receiver,
            });
            FnCallKind::Method
        } else {
            FnCallKind::Free
        };
        let end = loop {
            let name = if matches!(self.lex.nth(0).value, Token::Ident | Token::Keyword(_))
                && self.lex.nth(1).value == Token::Colon
            {
                let tok = self.lex.next();
                let name = self.make_ident(tok.span, lex::IdentContext::ParamPubName)?;
                self.expect(Token::Colon).unwrap();
                Some(name)
            } else {
                None
            };
            let value = self.maybe_expr(ExprState::block_start(lex::Block::Paren))?;
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
        let ty_params = self.maybe_ty_params()?;
        let ty = self.struct_type(true, true)?;

        let start = vis.as_ref().map(|v| v.span.start)
            .unwrap_or(name.span.start);
        let end = self.hir.node_kind(ty).span.end;
        Ok(self.hir.insert_struct(Span::new(start, end).spanned(Struct {
            vis,
            name,
            ty_params,
            ty,
        })))
    }

    fn type_alias(&mut self, vis: Option<S<Vis>>) -> PResult<NodeId> {
        self.expect(Token::Keyword(Keyword::Type))?;

        let name = self.ident()?;
        let ty_params = self.maybe_ty_params()?;
        self.expect(Token::Eq)?;
        let ty = self.ty_expr()?;
        self.expect(Token::Semi)?;

        let start = vis.as_ref().map(|v| v.span.start)
            .unwrap_or(name.span.start);
        let end = self.hir.node_kind(ty).span.end;
        Ok(self.hir.insert_type_alias(Span::new(start, end).spanned(TypeAlias {
            vis,
            name,
            ty_params,
            ty,
        })))
    }

    fn impl_(&mut self) -> PResult<NodeId> {
        let start = self.expect(Token::Keyword(Keyword::Impl))?.span.start;
        let ty_params = self.maybe_ty_params()?;
        let (trait_, for_) = if let Some(first) = self.maybe_path(true)? {
            if self.lex.maybe(Token::Keyword(Keyword::For)).is_some() {
                (Some(first), self.ty_expr()?)
            } else {
                let span = self.hir.node_kind(first).span;
                let for_ = self.hir.insert_ty_expr(span.spanned(TyExpr {
                    muta: None,
                    data: span.spanned(TyData::Path(first)),
                }));
                (None, for_)
            }
        } else {
            (None, self.ty_expr()?)
        };

        let span = self.hir.node_kind(for_).span;
        let for_ = self.hir.insert_type_alias(span.spanned(TypeAlias {
            vis: None,
            name: span.spanned(Ident::self_upper()),
            ty_params: Vec::new(),
            ty: for_,
        }));

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
            ty_params,
            trait_,
            for_,
            items,
        })))
    }

    fn struct_type(&mut self, named: bool, field_vis: bool) -> PResult<NodeId> {
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

        if !named_fields && !named && !delimited && fields.len() == 1 {
            return self.error(end, "expected `,`".into());
        }

        Ok(self.hir.insert_struct_type(Span::new(start, end.end).spanned(StructType {
            fields,
        })))
    }

    // Expects the first '{' be already consumed.
    fn block_or_struct_literal(&mut self, struct_name: Option<NodeId>, start: usize) -> PResult<NodeId> {
        enum Probe {
            StructStart {
                first_field: S<StructLiteralField>,
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
                first_field: Span::new(name.span.start, self.hir.node_kind(value).span.end).spanned(StructLiteralField {
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
                first_field: self.hir.node_kind(value).span.spanned(StructLiteralField {
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
                        first_field: self.hir.node_kind(value).span.spanned(StructLiteralField {
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
                fields.push(self.hir.insert_struct_literal_field(first_field));
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
                    fields.push(self.hir.insert_struct_literal_field(Span::new(start, value_span.end).spanned(
                        StructLiteralField {
                            name,
                            value,
                        })));
                }
                let end = self.expect(Token::BlockClose(lex::Block::Brace)).unwrap().span.end;

                self.hir.insert_struct_literal(Span::new(start, end).spanned(StructLiteral {
                    name: struct_name,
                    explicit_tuple,
                    fields,
                }))
            }
            Probe::EmptyStruct { end } => {
                self.hir.insert_struct_literal(Span::new(start, end).spanned(StructLiteral {
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
        | FnDef
        | Module
        | Struct
        | StructType
        | TypeAlias // `;` is part of the `type T = X;` itself.
        | Use // `;` is part of the `use path;` itself.
        | While
        => false,

        | Cast
        | CtlFlowAbort
        | FieldAccess
        | FnCall
        | FnDefParam
        | Let
        | LetDef
        | Literal
        | Op
        | Path
        | PathSegment
        | PathEndEmpty
        | PathEndIdent
        | PathEndStar
        | Range
        | TyExpr
        | TypeParam
        | SliceLiteral
        | StructLiteral
        | StructLiteralField
        => true,
    }
}