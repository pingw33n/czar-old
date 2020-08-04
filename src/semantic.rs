pub mod discover_names;
pub mod resolve_names;
pub mod type_check;

fn fatal(span: crate::syntax::Span, s: impl std::fmt::Display) -> ! {
    panic!("[{}:{}] {}", span.start, span.end, s);
}
