mod lex;
pub mod parse;

use std::io;
use std::ops::Range;
use std::path::{Path as StdPath, PathBuf};

use lex::{Keyword, Lexer, Token};

pub use lex::{FloatLiteral, FloatTypeSuffix, IntLiteral, IntTypeSuffix};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span {
            start,
            end,
        }
    }

    pub fn range(self) -> Range<usize> {
        self.start..self.end
    }

    pub fn extended(self, end: usize) -> Self {
        assert!(end >= self.end);
        Self {
            start: self.start,
            end,
        }
    }

    pub fn shifted(self, delta: isize) -> Self {
        Self {
            start: (self.start as isize + delta) as usize,
            end: (self.end as isize + delta) as usize,
        }
    }

    pub fn spanned<T>(self, value: T) -> Spanned<T> {
        Spanned {
            span: self,
            value,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Spanned<T> {
    pub span: Span,
    pub value: T,
}

pub type S<T> = Spanned<T>;

impl<T> Spanned<T> {
    pub fn new(span: Span, value: T) -> Self {
        Self {
            span,
            value,
        }
    }

    pub fn as_ref(&self) -> Spanned<&T> {
        Spanned {
            span: self.span,
            value: &self.value,
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Spanned<U> {
        let value = f(self.value);
        Spanned {
            value,
            span: self.span,
        }
    }

    pub fn with_span(self, span: Span) -> Self {
        Self {
            span,
            value: self.value,
        }
    }

    pub fn with_value<U>(self, value: U) -> Spanned<U> {
        Spanned {
            value,
            span: self.span,
        }
    }
}
