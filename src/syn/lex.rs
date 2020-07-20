use enum_as_inner::EnumAsInner;
use if_chain::if_chain;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::convert::TryFrom;
use std::ops::Range;
use std::str::{Chars, FromStr};
use std::fmt;

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
    Match,
    Mod,
    Mut,
    Package,
    Pub,
    Return,
    SelfLower,
    SelfUpper,
    Static,
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
            "match" => Match,
            "mod" => Mod,
            "mut" => Mut,
            "package" => Package,
            "pub" => Pub,
            "return" => Return,
            "self" => SelfLower,
            "Self" => SelfUpper,
            "static" => Static,
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

pub struct Lexer<'a> {
    s: &'a str,
    chars: Chars<'a>,
    error_count: usize,
}

impl<'a> Lexer<'a> {
    pub fn new(s: &'a str) -> Self {
        Self {
            s,
            chars: s.chars(),
            error_count: 0,
        }
    }

    pub fn next(&mut self) -> Spanned<Token> {
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

    pub fn is_ok(&self) -> bool {
        self.error_count == 0
    }

    fn next0(&mut self) -> Spanned<Token> {
        let start = self.pos();
        let c = self.next_char();
        let tok = match c {
            '/' => match self.nth(0) {
                '/' => self.line_comment(),
                '*' => self.block_comment(start),
                _ => Token::Slash,
            }
            c if is_whitespace(c) => self.whitespace(),

            '(' => Token::BlockOpen(Block::Paren),
            '[' => Token::BlockOpen(Block::Bracket),
            '{' => Token::BlockOpen(Block::Brace),
            ')' => Token::BlockClose(Block::Paren),
            ']' => Token::BlockClose(Block::Bracket),
            '}' => Token::BlockClose(Block::Brace),

            '&' => if self.nth(0) == '&' {
                self.next_char();
                Token::AmpAmp
            } else {
                Token::Amp
            }
            '-' => if self.nth(0) == '>' {
                self.next_char();
                Token::RArrow
            } else {
                Token::Minus
            }
            '>' => match self.nth(0) {
                '=' => {
                    self.next_char();
                    Token::GtEq
                }
                '>' => {
                    self.next_char();
                    Token::GtGt
                }
                _ => Token::Gt,
            }
            '<' => match self.nth(0) {
                '=' => {
                    self.next_char();
                    Token::LtEq
                }
                '<' => {
                    self.next_char();
                    Token::LtLt
                }
                _ => Token::Lt,
            }
            '=' => match self.nth(0) {
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
            '.' => if self.nth(0) == '.' {
                self.next_char();
                match self.nth(0) {
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
            ':' => if self.nth(0) == ':' {
                self.next_char();
                Token::ColonColon
            } else {
                Token::Colon
            }

            '+' => Token::Plus,
            ';' => Token::Semi,
            '*' => Token::Star,
            ',' => Token::Comma,
            '|' => Token::Pipe,
            '%' => Token::Percent,

            '"' => self.string(start),

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

    fn nth(&self, i: usize) -> char {
        self.chars.clone().nth(i).unwrap_or(EOF)
    }

    fn skip_while(&mut self, f: impl Fn(char) -> bool) {
        while f(self.nth(0)) {
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
            match (c, self.nth(0)) {
                ('/', '*') => {
                    self.next_char();
                    depth += 1;
                }
                ('*', '/') => {
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
        let raw = if start_char == 'r' && self.nth(0) == '#' {
            self.next_char();
            true
        } else {
            false
        };
        self.skip_while(|c| match c {
            | 'a'..='z'
            | 'A'..='Z'
            | '0'..='9'
            | '_'
            => true,
            _ => false,
        });
        if raw {
            Token::Ident
        } else {
            let s = &self.s[start..self.pos()];
            s.parse::<Keyword>()
                .map(Token::Keyword)
                .unwrap_or(Token::Ident)
        }
    }

    fn unknown(&mut self, start: usize) -> Token {
        self.error(Span::new(start, start + 1), "unknown token");
        Token::Unknown
    }

    fn number(&mut self, first_digit: char, start: usize) -> Token {
        let radix = if_chain! {
            if first_digit == '0';
            if let Ok(radix) = Radix::try_from(self.nth(0));
            then {
                self.next_char();
                radix
            } else {
                Radix::Dec
            }
        };

        #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
        enum FloatPart {
            None,
            Frac,
            Exp,
        }
        let mut float_part = FloatPart::None;
        loop {
            match self.nth(0) {
                'e' | 'E' => if radix == Radix::Dec {
                    self.next_char();
                    if float_part < FloatPart::Exp {
                        float_part = FloatPart::Exp;
                        match self.nth(0) {
                            '+' | '-' => {
                                self.next_char();
                            }
                            _ => {}
                        }
                    }
                }
                '.' => {
                    if float_part == FloatPart::None {
                        if is_ident_start(self.nth(1)) {
                            // 0.abs
                            break;
                        }
                        float_part = FloatPart::Frac;
                    } else {
                        // 0.1.0
                        // 0.1.abs
                        break;
                    }
                }
                '0'..='9' | 'A'..='Z' | 'a'..='z' | '_' => {}
                _ => break,
            }
            self.next_char();
        }
        let lit = if float_part == FloatPart::None {
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

#[derive(Debug)]
pub struct StringLiteralError {
    pub pos: usize,
    pub kind: StringErrorKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StringErrorKind {
    BadEscape,
    BadUnicodeEscape,
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

    fn detect(s: &str) -> Option<Self> {
        for (i, &suff) in INT_TYPE_SUFFIXES.iter().enumerate() {
            if s.ends_with(suff) {
                return Some(Self::try_from(i as u32).unwrap());
            }
        }
        None
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
        let ty = IntTypeSuffix::detect(s);
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

pub fn string_literal(s: &str) -> Result<String, StringLiteralError> {
    assert!(s.len() >= 2);
    assert_eq!(s.as_bytes()[0], b'"');
    assert_eq!(s.as_bytes()[s.len() - 1], b'"');

    let mut r = String::with_capacity(s.len());
    let mut it = s[1..s.len() - 1].char_indices()
        .map(|(i, c)| (i + 1, c));

    while let Some((_, c)) = it.next() {
        match c {
            '\\' => {
                let (pos, c) = it.next().unwrap();
                match c {
                    '\\' | '\'' | '"' => r.push(c),
                    'r' => r.push('\r'),
                    'n' => r.push('\n'),
                    't' => r.push('\t'),
                    'x' => {
                        let (pos, h) = it.next().unwrap();
                        let l = it.next().unwrap().1;
                        let v = hex2_to_dec(h, l);
                        if let Some(v) = v.filter(|&v| v <= 0x7f) {
                            r.push(v as char);
                        } else {
                            return Err(StringLiteralError { pos, kind: StringErrorKind::BadEscape });
                        }
                    }
                    '\n' => {}
                    '\r' => {
                        assert_eq!(it.next().unwrap().1, '\n');
                    }
                    'u' => {
                        let c = it.next();
                        if c.is_none() || c.unwrap().1 != '{' {
                            return Err(StringLiteralError { pos, kind: StringErrorKind::BadUnicodeEscape })
                        }
                        let mut digs = [0; 6];
                        let mut digs_len = 0;
                        loop {
                            match it.next() {
                                Some((_, c)) => {
                                    match c {
                                        '}' => break,
                                        _ if digs_len < digs.len() && c.is_ascii_hexdigit() => {
                                            digs[digs_len] = c as u8;
                                            digs_len += 1;
                                        }
                                        _ => {
                                            return Err(StringLiteralError { pos, kind: StringErrorKind::BadUnicodeEscape })
                                        }
                                    }
                                }
                                None => return Err(StringLiteralError { pos, kind: StringErrorKind::BadUnicodeEscape }),
                            }
                        }
                        if digs_len == 0 {
                            return Err(StringLiteralError { pos, kind: StringErrorKind::BadUnicodeEscape });
                        }
                        // The unwraps below should never panic.
                        let digs = std::str::from_utf8(&digs[..digs_len]).unwrap();
                        let c = u32::from_str_radix(digs, 16).unwrap();
                        if let Ok(c) = char::try_from(c) {
                            r.push(c);
                        } else {
                            return Err(StringLiteralError { pos, kind: StringErrorKind::BadUnicodeEscape });
                        }
                    }
                    _ => return Err(StringLiteralError { pos, kind: StringErrorKind::BadEscape }),
                }
            }
            '\r' => {
                // Normalize line ending.
                assert_eq!(it.next().unwrap().1, '\n');
                r.push('\n');
            }
            _ => r.push(c),
        }
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

        use StringErrorKind::*;
        for (inp, exp) in &[
            (q(r"\u"), BadUnicodeEscape),
            (q(r"\u{"), BadUnicodeEscape),
            (q(r"\u{0"), BadUnicodeEscape),
            (q(r"\u0"), BadUnicodeEscape),
            (q(r"\u{110000}"), BadUnicodeEscape),
        ] {
            assert_eq!(string_literal(&inp).unwrap_err().kind, *exp);
        }
    }
}
