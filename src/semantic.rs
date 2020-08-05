pub mod discover;
pub mod resolve;
pub mod type_check;

fn fatal(span: crate::syntax::Span, s: impl std::fmt::Display) -> ! {
    panic!("[{}:{}] {}", span.start, span.end, s);
}
