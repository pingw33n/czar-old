mod lex;
pub mod parse;

use std::io;
use std::path::{Path as StdPath, PathBuf};

use lex::{Keyword, Lexer, Token};

pub use lex::{FloatLiteral, FloatTypeSuffix, IntLiteral, IntTypeSuffix, S, Span, Spanned};

pub fn source_file_name(mod_name: &str) -> PathBuf {
    format!("{}.cz", mod_name).into()
}