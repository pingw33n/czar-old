use arrayvec::ArrayVec;
use enum_as_inner::EnumAsInner;
use if_chain::if_chain;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::convert::TryFrom;
use std::ops::Range;
use std::str::{Chars, FromStr};
use std::fmt;
use std::collections::VecDeque;

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

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, PartialEq)]
pub enum Token {
    Eof,
    Unknown,

    BlockClose(Block),
    BlockOpen(Block),
    Comment,
    Ident,
    Label,
    Keyword(Keyword),
    Literal(Literal),

    Whitespace,

    /// &&
    AmpAmp,
    /// :
    ColonColon,
    /// ..
    DotDot,
    /// ...
    DotDotDot,
    /// ..=
    DotDotEq,
    /// ==
    EqEq,
    /// !=
    ExclEq,
    /// =>
    FatArrow,
    /// >=
    GtEq,
    /// >>
    GtGt,
    /// <=
    LtEq,
    /// <<
    LtLt,
    /// ->
    RArrow,
    /// +=
    PlusEq,
    /// -=
    MinusEq,
    /// /=
    SlashEq,
    /// *=
    StarEq,
    /// %=
    PercentEq,
    /// &=
    AmpEq,
    /// |=
    PipeEq,
    /// ||
    PipePipe,
    /// ^=
    HatEq,
    /// >>=
    GtGtEq,
    /// <<=
    LtLtEq,

    /// &
    Amp,
    /// :
    Colon,
    /// ,
    Comma,
    /// .
    Dot,
    /// =
    Eq,
    /// <
    Lt,
    /// >
    Gt,
    /// -
    Minus,
    /// %
    Percent,
    /// |
    Pipe,
    /// +
    Plus,
    /// ;
    Semi,
    /// /
    Slash,
    /// *
    Star,
    /// !
    Excl,
    /// ?
    Quest,
    /// ^
    Hat,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Keyword {
    As,
    Break,
    Continue,
    Const,
    Dyn,
    Else,
    Enum,
    False,
    For,
    Fn,
    If,
    In,
    Is,
    Impl,
    Let,
    Loop,
    Match,
    Mod,
    Mut,
    Package,
    Pub,
    Ref,
    Return,
    SelfLower,
    SelfUpper,
    Static,
    Struct,
    Super,
    Trait,
    True,
    Try,
    Type,
    Underscore,
    Union,
    Unsafe,
    Use,
    Where,
    While,
}

impl FromStr for Keyword {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use Keyword::*;
        Ok(match s {
            "as" => As,
            "break" => Break,
            "continue" => Continue,
            "const" => Const,
            "dyn" => Dyn,
            "else" => Else,
            "enum" => Enum,
            "false" => False,
            "for" => For,
            "fn" => Fn,
            "if" => If,
            "in" => In,
            "is" => Is,
            "impl" => Impl,
            "let" => Let,
            "loop" => Loop,
            "match" => Match,
            "mod" => Mod,
            "mut" => Mut,
            "package" => Package,
            "pub" => Pub,
            "ref" => Ref,
            "return" => Return,
            "self" => SelfLower,
            "Self" => SelfUpper,
            "static" => Static,
            "struct" => Struct,
            "super" => Super,
            "trait" => Trait,
            "true" => True,
            "try" => Try,
            "type" => Type,
            "_" => Underscore,
            "union" => Union,
            "unsafe" => Unsafe,
            "use" => Use,
            "where" => Where,
            "while" => While,
            _ => return Err(()),
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Block {
    // ( )
    Paren,
    // [ ]
    Bracket,
    // { }
    Brace,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Literal {
    Int,
    Float,
    String,
    Char,
}

const EOF: char = '\0';

struct SavedState<'a> {
    chars: Chars<'a>,
    error_count: usize,
    saved_buf: usize,
}

pub struct SavedStateId {
    i: Option<usize>,
}

impl Drop for SavedStateId {
    fn drop(&mut self) {
        if std::thread::panicking() {
            return;
        }
        if let Some(i) = self.i.take() {
            panic!("Lexer saved state {} wasn't restored or discarded", i);
        }
    }
}

pub struct Lexer<'a> {
    s: &'a str,
    chars: Chars<'a>,
    buf: VecDeque<S<Token>>,
    error_count: usize,
    saved_states: Vec<SavedState<'a>>,
    saved_bufs: Vec<S<Token>>,
}

impl<'a> Lexer<'a> {
    pub fn new(s: &'a str) -> Self {
        Self {
            s,
            chars: s.chars(),
            buf: VecDeque::new(),
            saved_states: Vec::new(),
            saved_bufs: Vec::new(),
            error_count: 0,
        }
    }

    #[must_use]
    pub fn nth(&mut self, i: usize) -> S<Token> {
        self.fill_buf(i + 1);
        self.buf[i]
    }

    #[must_use]
    pub fn next(&mut self) -> S<Token> {
        let r = self.nth(0);
        self.buf.pop_front().unwrap();
        r
    }

    pub fn consume(&mut self) {
        let _ = self.next();
    }

    pub fn maybe(&mut self, tok: Token) -> Option<S<Token>> {
        if self.nth(0).value == tok {
            Some(self.next())
        } else {
            None
        }
    }

    pub fn insert(&mut self, tok: S<Token>) {
        self.buf.insert(0, tok);
    }

    pub fn save_state(&mut self) -> SavedStateId {
        self.saved_states.push(SavedState {
            chars: self.chars.clone(),
            error_count: self.error_count,
            saved_buf: self.saved_bufs.len(),
        });
        self.saved_bufs.extend(&self.buf);
        SavedStateId { i: Some(self.saved_states.len()) }
    }

    pub fn restore_state(&mut self, mut id: SavedStateId) {
        assert_eq!(id.i.take(), Some(self.saved_states.len()));
        let state = self.saved_states.pop().unwrap();
        assert!(state.saved_buf <= self.saved_bufs.len());
        self.chars = state.chars;
        self.error_count = state.error_count;
        self.buf.clear();
        self.buf.extend(self.saved_bufs.drain(state.saved_buf..));
        self.saved_bufs.truncate(state.saved_buf);
    }

    pub fn discard_state(&mut self, mut id: SavedStateId) {
        assert_eq!(id.i.take(), Some(self.saved_states.len()));
        let state = self.saved_states.pop().unwrap();
        assert!(state.saved_buf <= self.saved_bufs.len());
        self.saved_bufs.truncate(state.saved_buf);
    }

    pub fn is_ok(&self) -> bool {
        self.error_count == 0
    }

    fn fill_buf(&mut self, len: usize) {
        while self.buf.len() < len {
            let tok = self.next_meaningful();
            self.buf.push_back(tok);
        }
    }

    fn next_meaningful(&mut self) -> S<Token> {
        loop {
            let r = self.next0();
            match r.value {
                | Token::Whitespace
                | Token::Comment
                | Token::Unknown
                => {}
                _ => break r,
            }
        }
    }

    fn next0(&mut self) -> S<Token> {
        let start = self.pos();
        let c = self.next_char();
        let tok = match c {
            '/' => match self.nth_char(0) {
                '/' => self.line_comment(),
                '*' => self.block_comment(start),
                '=' => {
                    self.next_char();
                    Token::SlashEq
                }
                _ => Token::Slash,
            }
            c if is_whitespace(c) => self.whitespace(),

            '(' => Token::BlockOpen(Block::Paren),
            '[' => Token::BlockOpen(Block::Bracket),
            '{' => Token::BlockOpen(Block::Brace),
            ')' => Token::BlockClose(Block::Paren),
            ']' => Token::BlockClose(Block::Bracket),
            '}' => Token::BlockClose(Block::Brace),

            '&' => match self.nth_char(0) {
                '&' => {
                    self.next_char();
                    Token::AmpAmp
                }
                '=' => {
                    self.next_char();
                    Token::AmpEq
                }
                _ => Token::Amp,
            }
            '-' => match self.nth_char(0) {
                '>' => {
                    self.next_char();
                    Token::RArrow
                }
                '=' => {
                    self.next_char();
                    Token::MinusEq
                }
                _ => Token::Minus,
            }
            '>' => match self.nth_char(0) {
                '=' => {
                    self.next_char();
                    Token::GtEq
                }
                '>' => {
                    self.next_char();
                    if self.nth_char(0) == '=' {
                        self.next_char();
                        Token::GtGtEq
                    } else {
                        Token::GtGt
                    }
                }
                _ => Token::Gt,
            }
            '<' => match self.nth_char(0) {
                '=' => {
                    self.next_char();
                    Token::LtEq
                }
                '<' => {
                    self.next_char();
                    if self.nth_char(0) == '=' {
                        self.next_char();
                        Token::LtLtEq
                    } else {
                        Token::LtLt
                    }
                }
                _ => Token::Lt,
            }
            '=' => match self.nth_char(0) {
                '=' => {
                    self.next_char();
                    Token::EqEq
                }
                '>' => {
                    self.next_char();
                    Token::FatArrow
                }
                _ => Token::Eq,
            }
            '.' => if self.nth_char(0) == '.' {
                self.next_char();
                match self.nth_char(0) {
                    '.' => {
                        self.next_char();
                        Token::DotDotDot
                    }
                    '=' => {
                        self.next_char();
                        Token::DotDotEq
                    }
                    _ => Token::DotDot,
                }
            } else {
                Token::Dot
            }
            ':' => if self.nth_char(0) == ':' {
                self.next_char();
                Token::ColonColon
            } else {
                Token::Colon
            }
            '!' => if self.nth_char(0) == '=' {
                self.next_char();
                Token::ExclEq
            } else {
                Token::Excl
            }
            '+' => if self.nth_char(0) == '=' {
                self.next_char();
                Token::PlusEq
            } else {
                Token::Plus
            }
            '*' => if self.nth_char(0) == '=' {
                self.next_char();
                Token::StarEq
            } else {
                Token::Star
            }
            '|' => match self.nth_char(0) {
                '=' => {
                    self.next_char();
                    Token::PipeEq
                }
                '|' => {
                    self.next_char();
                    Token::PipePipe
                }
                _ => Token::Pipe,
            }
            '%' => if self.nth_char(0) == '=' {
                self.next_char();
                Token::PercentEq
            } else {
                Token::Percent
            }
            '^' => if self.nth_char(0) == '=' {
                self.next_char();
                Token::HatEq
            } else {
                Token::Hat
            }

            ';' => Token::Semi,
            ',' => Token::Comma,
            '?' => Token::Quest,
            '"' => self.string(start),
            '\'' => self.char(start),

            '@' if is_ident_start(self.nth_char(0)) => self.label(),

            c if c.is_ascii_digit() => self.number(c, start),

            c if is_ident_start(c) => self.ident_or_keyword(c, start),

            EOF => Token::Eof,

            _ => self.unknown(start),
        };
        Spanned::new(Span::new(start, self.pos()), tok)
    }

    fn pos(&self) -> usize {
        self.s.len() - self.chars.as_str().len()
    }

    fn next_char(&mut self) -> char {
        self.chars.next().unwrap_or(EOF)
    }

    fn nth_char(&self, i: usize) -> char {
        self.chars.clone().nth(i).unwrap_or(EOF)
    }

    fn skip_while(&mut self, f: impl Fn(char) -> bool) {
        while f(self.nth_char(0)) {
            if self.next_char() == EOF {
                break;
            }
        }
    }

    fn error(&mut self, span: Span, msg: &str) {
        eprintln!("({}..{}) {}", span.start, span.end, msg);
        self.error_count += 1;
    }

    fn line_comment(&mut self) -> Token {
        self.next_char();
        self.skip_while(|c| c != '\n');
        Token::Comment
    }

    fn block_comment(&mut self, start: usize) -> Token {
        self.next_char();
        let mut depth = 1;
        loop {
            let c = self.next_char();
            match (c, self.nth_char(0)) {
                ('/', '*') => {
                    self.next_char();
                    depth += 1;
                }
                ('*', '/') => {
                    self.next_char();
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                (EOF, _) => break,
                _ => {}
            }
        }

        if depth != 0 {
            self.error(Span::new(start, self.pos()), "unterminated block comment");
        }

        Token::Comment
    }

    fn whitespace(&mut self) -> Token {
        self.skip_while(is_whitespace);
        Token::Whitespace
    }

    fn ident_or_keyword(&mut self, start_char: char, start: usize) -> Token {
        let raw = if start_char == 'r' && self.nth_char(0) == '#' {
            self.next_char();
            true
        } else {
            false
        };
        self.skip_while(is_ident_middle);
        if raw {
            Token::Ident
        } else {
            let s = &self.s[start..self.pos()];
            s.parse::<Keyword>()
                .map(Token::Keyword)
                .unwrap_or(Token::Ident)
        }
    }

    fn label(&mut self) -> Token {
        self.next_char();
        self.skip_while(is_ident_middle);
        Token::Label
    }

    fn unknown(&mut self, start: usize) -> Token {
        self.error(Span::new(start, start + 1), "unknown token");
        Token::Unknown
    }

    fn number(&mut self, first_digit: char, start: usize) -> Token {
        let radix = if_chain! {
            if first_digit == '0';
            if let Ok(radix) = Radix::try_from(self.nth_char(0));
            then {
                self.next_char();
                radix
            } else {
                Radix::Dec
            }
        };

        #[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
        enum FloatPart {
            None,
            Frac,
            ExpStart,
            ExpMiddle,
        }
        let mut float_part = FloatPart::None;
        loop {
            match self.nth_char(0) {
                'e' | 'E' => if radix == Radix::Dec {
                    if float_part < FloatPart::ExpStart {
                        float_part = FloatPart::ExpStart;
                        match self.nth_char(1) {
                            '+' | '-' => {
                                self.next_char();
                                float_part = FloatPart::ExpMiddle;
                            }
                            _ => {}
                        }
                    }
                }
                '.' => {
                    if float_part == FloatPart::None {
                        let next = self.nth_char(1);
                        if is_ident_start(next) || next == '.' {
                            // 0.abs
                            // 0..10
                            break;
                        }
                        float_part = FloatPart::Frac;
                    } else {
                        // 0.1.0
                        // 0.1.abs
                        break;
                    }
                }
                '0'..='9' => {
                    if float_part == FloatPart::ExpStart {
                        float_part = FloatPart::ExpMiddle;
                    }
                }
                'A'..='Z' | 'a'..='z' | '_' => {}
                _ => break,
            }
            self.next_char();
        }
        let lit = if float_part == FloatPart::ExpStart
            && self.s[start..self.pos()].parse::<IntTypeSuffix>().is_ok()
        {
            Literal::Int
        } else if float_part == FloatPart::None {
            if let Ok(_) = self.s[start..self.pos()].parse::<FloatTypeSuffix>() {
                Literal::Float
            } else {
                Literal::Int
            }
        } else {
            Literal::Float
        };
        Token::Literal(lit)
    }

    fn string(&mut self, start: usize) -> Token {
        loop {
            let c = self.next_char();
            match c {
                EOF => {
                    self.error(Span::new(start, self.pos()), "unterminated string");
                    break;
                }
                '"' => break,
                '\\' => { self.next_char(); }
                '\r' => match self.next_char() {
                    EOF => {} // report as unterminated
                    '\n' => {},
                    _ => {
                        let p = self.pos();
                        self.error(Span::new(p - 1, p), "invalid line ending");
                        break;
                    }
                }
                _ => {}
            }
        }
        Token::Literal(Literal::String)
    }

    fn char(&mut self, start: usize) -> Token {
        loop {
            let c = self.next_char();
            match c {
                '\n' | '\r' | EOF => {
                    self.error(Span::new(start, self.pos()), "unterminated char literal");
                    break;
                }
                '\\' => { self.next_char(); }
                '\'' => break,
                _ => {}
            }
        }
        Token::Literal(Literal::Char)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Radix {
    Bin = 2,
    Dec = 10,
    Hex = 16,
}

impl TryFrom<char> for Radix {
    type Error = ();

    fn try_from(c: char) -> Result<Self, Self::Error> {
        Ok(match c {
            'b' | 'B' => Radix::Bin,
            'x' | 'X' => Radix::Hex,
            _ => return Err(()),
        })
    }
}

static INT_TYPE_SUFFIXES: [&str; 12] = [
    "i8",
    "u8",
    "i16",
    "u16",
    "i32",
    "u32",
    "i64",
    "u64",
    "i128",
    "u128",
    "isize",
    "usize",
];

#[derive(Clone, Copy, Debug, Eq, IntoPrimitive, PartialEq, TryFromPrimitive)]
#[repr(u32)]
pub enum IntTypeSuffix {
    I8 = 0,
    U8 = 1,
    I16 = 2,
    U16 = 3,
    I32 = 4,
    U32 = 5,
    I64 = 6,
    U64 = 7,
    I128 = 8,
    U128 = 9,
    Isize = 10,
    Usize = 11,
}

impl IntTypeSuffix {
    pub fn as_str(self) -> &'static str {
        INT_TYPE_SUFFIXES[u32::from(self) as usize]
    }

    pub fn is_signed(self) -> bool {
        match self.as_str().as_bytes()[0] {
            b'i' => true,
            b'u' => false,
            _ => unreachable!(),
        }
    }
}

impl FromStr for IntTypeSuffix {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        for (i, &suff) in INT_TYPE_SUFFIXES.iter().enumerate() {
            if s.ends_with(suff) {
                return Ok(Self::try_from(i as u32).unwrap());
            }
        }
        Err(())
    }
}

impl fmt::Display for IntTypeSuffix {
   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
       f.write_str(self.as_str())
   }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntLiteralError {
    BadUnderscorePlace,
    Incomplete,
    Invalid,
    OutOfRange,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IntLiteral {
    pub value: u128,
    pub ty: Option<IntTypeSuffix>,
}

impl FromStr for IntLiteral {
    type Err = IntLiteralError;

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        let ty = s.parse::<IntTypeSuffix>().ok();
        if let Some(ty) = ty {
            s = &s[..s.len() - ty.as_str().len()];
        }

        let mut c = s.chars();
        let (c1, c2) = (c.next(), c.next());
        let radix = if_chain! {
            if let (Some(c1), Some(c2)) = (c1, c2);
            if c1 == '0';
            if let Ok(radix) = Radix::try_from(c2);
            then {
                s = &s[2..];
                radix
            } else {
                Radix::Dec
            }};

        if s.is_empty() {
            return Err(IntLiteralError::Incomplete);
        }

        let mut buf = [0; 64];
        let buf_len = match deunderscore(s, ty.is_some(),
            |c, i| if i < buf.len() { buf[i] = c; true } else { false })
        {
            Ok(v) => v,
            Err(e) => return Err(match e {
                DeunderscoreErr::BufOverflow => IntLiteralError::OutOfRange,
                DeunderscoreErr::BadUnderscorePlace => IntLiteralError::BadUnderscorePlace,
            }),
        };

        match u128::from_str_radix(std::str::from_utf8(&buf[..buf_len]).unwrap(), radix as u32) {
            Ok(value) => Ok(Self { value, ty }),
            Err(_) => Err(IntLiteralError::Invalid),
        }
    }
}

static FLOAT_TYPE_SUFFIXES: [&str; 2] = [
    "f32",
    "f64",
];

#[derive(Clone, Copy, Debug, Eq, IntoPrimitive, PartialEq, TryFromPrimitive)]
#[repr(u32)]
pub enum FloatTypeSuffix {
    F32 = 0,
    F64 = 1,
}

impl FloatTypeSuffix {
    pub fn as_str(self) -> &'static str {
        FLOAT_TYPE_SUFFIXES[u32::from(self) as usize]
    }
}

impl FromStr for FloatTypeSuffix {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        for (i, &suff) in FLOAT_TYPE_SUFFIXES.iter().enumerate() {
            if s.ends_with(suff) {
                return Ok(Self::try_from(i as u32).unwrap());
            }
        }
        Err(())
    }
}

impl fmt::Display for FloatTypeSuffix {
   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
       f.write_str(self.as_str())
   }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FloatLiteralError {
    BadUnderscorePlace,
    Invalid,
    OutOfRange,
}

#[derive(Clone, Copy, Debug)]
pub struct FloatLiteral {
    pub value: f64,
    pub ty: Option<FloatTypeSuffix>,
}

impl FromStr for FloatLiteral {
    type Err = FloatLiteralError;

    fn from_str(mut s: &str) -> Result<Self, Self::Err> {
        let ty = s.parse::<FloatTypeSuffix>().ok();
        if let Some(ty) = ty {
            s = &s[..s.len() - ty.as_str().len()];
        }

        let mut buf = String::new();
        match deunderscore(s, ty.is_some(), |c, _| { buf.push(c as char); true }) {
            Ok(v) => v,
            Err(e) => return Err(match e {
                DeunderscoreErr::BufOverflow => FloatLiteralError::OutOfRange,
                DeunderscoreErr::BadUnderscorePlace => FloatLiteralError::BadUnderscorePlace,
            }),
        };

        match buf.parse::<f64>() {
            Ok(v) if v.is_infinite() || v.is_nan() => Err(FloatLiteralError::OutOfRange),
            Ok(value) => Ok(Self { value, ty }),
            Err(_) => Err(FloatLiteralError::Invalid),
        }
    }
}

#[derive(Clone, Copy)]
enum DeunderscoreErr {
    BufOverflow,
    BadUnderscorePlace,
}

fn deunderscore(s: &str, had_suffix: bool, mut buf: impl FnMut(u8, usize) -> bool)
    -> Result<usize, DeunderscoreErr>
{
    let mut i = 0;
    let mut it = s.as_bytes().iter().copied().peekable();
    while let Some(c) = it.next() {
        match c {
            b'_' => {
                match it.peek() {
                    | Some(b'_')
                    | Some(b'.')
                    => return Err(DeunderscoreErr::BadUnderscorePlace),
                    None if !had_suffix => return Err(DeunderscoreErr::BadUnderscorePlace),
                    _ => {}
                }
            }
            _ => {
                if !buf(c, i) {
                    return Err(DeunderscoreErr::BufOverflow);
                }
                i += 1;
            }
        }
    }
    Ok(i)
}

fn decode_literal_char(it: &mut Chars, newline_escape: bool) -> Result<Option<char>, ()> {
    Ok(Some(loop {
        let c = if let Some(c) = it.next() {
            c
        } else {
            return Ok(None);
        };
        break match c {
            '\\' => {
                let c = it.next().ok_or(())?;
                match c {
                    | '\\'
                    | '\''
                    | '"'
                    => c,
                    't' => '\t',
                    'n' => '\n',
                    'r' => '\r',
                    'x' => {
                        let h = it.next().ok_or(())?;
                        let l = it.next().ok_or(())?;
                        let v = hex2_to_dec(h, l);
                        if let Some(v) = v.filter(|&v| v <= 0x7f) {
                            v as char
                        } else {
                            return Err(());
                        }
                    }
                    '\n' => {
                        assert!(newline_escape);
                        continue;
                    }
                    '\r' => {
                        assert!(newline_escape);
                        assert_eq!(it.next().ok_or(())?, '\n');
                        continue;
                    }
                    'u' => {
                        it.next()
                            .filter(|&c| c == '{')
                            .ok_or(())?;
                        let mut digs = ArrayVec::<[_; 6]>::new();
                        loop {
                            match it.next().ok_or(())? {
                                '}' => break,
                                c if c.is_ascii_hexdigit() => {
                                    digs.try_push(c as u8).map_err(|_| {})?;
                                }
                                _ => {
                                    return Err(())
                                }
                            }
                        }
                        if digs.is_empty() {
                            return Err(());
                        }
                        // The unwraps below should never panic.
                        let digs = std::str::from_utf8(&digs).unwrap();
                        let c = u32::from_str_radix(digs, 16).unwrap();
                        if let Ok(c) = char::try_from(c) {
                            c
                        } else {
                            return Err(());
                        }
                    }
                    _ => return Err(()),
                }
            }
            '\r' => {
                assert!(newline_escape);
                // Normalize line ending.
                assert_eq!(it.next().ok_or(())?, '\n');
                '\n'
            }
            _ => c,
        };
    }))
}

#[derive(Debug)]
pub struct CharLiteralError;

pub fn char_literal(s: &str) -> Result<char, CharLiteralError> {
    assert!(s.len() >= 3);
    assert_eq!(s.as_bytes()[0], b'\'');
    assert_eq!(s.as_bytes()[s.len() - 1], b'\'');
    let mut it = s[1..s.len() - 1].chars();
    let c = decode_literal_char(&mut it, false)
        .map_err(|_| CharLiteralError)?
        .unwrap();
    if it.next().is_none() {
        Ok(c)
    } else {
        Err(CharLiteralError)
    }
}

#[derive(Debug)]
pub struct StringLiteralError;

pub fn string_literal(s: &str) -> Result<String, StringLiteralError> {
    assert!(s.len() >= 2);
    assert_eq!(s.as_bytes()[0], b'"');
    assert_eq!(s.as_bytes()[s.len() - 1], b'"');

    let mut r = String::with_capacity(s.len());
    let mut it = s[1..s.len() - 1].chars();
    while let Some(c) = decode_literal_char(&mut it, true)
        .map_err(|_| StringLiteralError)?
    {
        r.push(c);
    }

    Ok(r)
}

pub fn ident(s: &str) -> String {
    if s.starts_with("r#") {
        &s[2..]
    } else {
        s
    }.into()
}

pub fn label(s: &str) -> String {
    assert!(s.len() > 1);
    assert_eq!(s.as_bytes()[0], b'@');
    s[1..].into()
}

fn is_whitespace(c: char) -> bool {
    match c {
        | '\u{0009}' // \t
        | '\u{000A}' // \n
        | '\u{000B}' // vertical tab
        | '\u{000C}' // form feed
        | '\u{000D}' // \r
        | '\u{0020}' // space
        => true,
        _ => false,
    }
}

fn is_ident_start(c: char) -> bool {
    match c {
        | 'a'..='z'
        | 'A'..='Z'
        | '_'
        => true,
        _ => false,
    }
}

fn is_ident_middle(c: char) -> bool {
    match c {
        | 'a'..='z'
        | 'A'..='Z'
        | '0'..='9'
        | '_'
        => true,
        _ => false,
    }
}

fn hex1_to_dec(c: char) -> Option<u8> {
    Some(match c {
        '0'..='9' => c as u8 - b'0',
        'A'..='F' => 10 + c as u8 - b'A',
        'a'..='f' => 10 + c as u8 - b'a',
        _ => return None,
    })
}

fn hex2_to_dec(c1: char, c2: char) -> Option<u8> {
    Some((hex1_to_dec(c1)? << 4) | hex1_to_dec(c2)?)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn hex1_to_dec_() {
        let s = "0123456789abcdef";
        for s in &[s.to_ascii_lowercase(), s.to_ascii_uppercase()] {
            for (exp, inp) in s.chars().enumerate() {
                assert_eq!(hex1_to_dec(inp), Some(exp as u8));
            }
        }
    }

    #[test]
    fn string_literal_ok() {
        fn q(s: &str) -> String { format!("\"{}\"", s) }

        for (inp, exp) in &[
            (q("test перевірка 单元测试"), "test перевірка 单元测试"),
            (q("\r\n\r\n\n"), "\n\n\n"),
            (q("foo\\\n  bar \\\r\nbaz"), "foo  bar baz"),
            (q(r"\u{0}\u{10FFFF}"), "\u{0}\u{10FFFF}")
        ] {
            assert_eq!(string_literal(&inp).unwrap(), exp.to_string());
        }
    }

    #[test]
    fn string_literal_err() {
        fn q(s: &str) -> String { format!("\"{}\"", s) }

        for inp in &[
            q(r"\u"),
            q(r"\u{"),
            q(r"\u{0"),
            q(r"\u0"),
            q(r"\u{110000}"),
        ] {
            assert!(string_literal(&inp).is_err());
        }
    }
}
