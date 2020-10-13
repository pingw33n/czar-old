use std::fmt::{Result, Write};
use std::path::Path;

use crate::hir::{self, SourceId, Sources};
use crate::syntax::Span;

#[derive(Clone, Copy, Debug)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Debug)]
pub struct Source {
    pub id: SourceId,
    pub span: Span,
}

#[derive(Debug)]
pub struct Report {
    pub severity: Severity,
    pub text: String,
    pub source: Option<Source>,
}

pub struct SaveState {
    len: usize,
}

#[derive(Default)]
pub struct Diag {
    reports: Vec<Report>,
}

impl Diag {
    pub fn report(&mut self, report: Report) {
        self.reports.push(report);
    }

    pub fn reports(&self) -> &[Report] {
        &self.reports
    }

    pub fn save_state(&self) -> SaveState {
        SaveState {
            len: self.reports.len(),
        }
    }

    pub fn restore_state(&mut self, state: SaveState) {
        assert!(self.reports.len() >= state.len);
        self.reports.truncate(state.len);
    }

    pub fn print(&self, base_dir: impl AsRef<Path>, out: &mut impl Write, sources: &Sources) -> Result {
        for (i, Report { severity, text, source }) in self.reports.iter().enumerate() {
            if i > 0 {
                writeln!(out)?;
            }
            let severity = match severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            writeln!(out, "{}: {}", severity, text)?;
            if let &Some(Source { id, span }) = source {
                let source = &sources[id];
                // TODO build and use line index
                let hi_line = HiLine::from_span(span, source);

                let path = source.path.strip_prefix(base_dir.as_ref()).unwrap_or(&source.path);
                writeln!(out, "  --> {}:{}:{}",
                    path.to_string_lossy(),
                    hi_line.num,
                    hi_line.col_start + 1)?;
                hi_line.print(out, source)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
struct HiLine {
    whole: Span,
    num: u32,
    col_start: u32,
    col_len: u32,
}

impl HiLine {
    fn from_span(span: Span, source: &hir::Source) -> Self {
        let s = source.text.as_str();
        assert!(!span.is_empty());
        assert!(span.end <= s.len());

        let mut it = s.char_indices().peekable();
        let mut num = 1;
        let mut line_start = 0;
        let mut r = None;
        while let Some((i, c)) = it.next() {
            if r.is_none() {
                if i == span.start {
                    let col_start = (i - line_start) as u32;
                    r = Some(HiLine {
                        whole: Span::new(line_start, line_start),
                        num,
                        col_start,
                        col_len: 0,
                    });
                } else {
                    assert!(i < span.start);
                }
            }

            if i == span.end {
                if let Some(l) = r.as_mut() {
                    l.col_len = (i - line_start) as u32 - l.col_start;
                }
            }
            let nl = match c {
                '\n' => Some(1),
                '\r' if it.peek().map(|&(_, c)| c) == Some('\n') => {
                    it.next().unwrap();
                    Some(2)
                }
                _ => None
            };
            let eof = it.peek().is_none();
            if nl.is_some() || eof {
                if let Some(l) = r.as_mut() {
                    l.whole.end = i + if eof { 1 } else { 0 };
                    if l.col_len == 0 {
                        l.col_len = (i - line_start) as u32 - l.col_start;
                    }
                    break;
                }
            }
            if let Some(nl) = nl {
                num += 1;
                line_start = i + nl;
            }
        }
        r.unwrap()
    }

    fn print(&self, out: &mut impl Write, source: &hir::Source) -> Result {
        let line_num_width = digit_count(self.num);
        let line_num = self.num.to_string();
        for _ in 0..line_num.len() - line_num_width as usize {
            write!(out, " ")?;
        }
        writeln!(out, "{} | {}", line_num, &source.text[self.whole.start..self.whole.end])?;

        let hi_start = line_num_width + 3 + self.col_start;
        for _ in 0..hi_start {
            write!(out, " ")?;
        }
        for _ in 0..self.col_len {
            write!(out, "~")?;
        }
        writeln!(out)
    }
}

fn digit_count(mut n: u32) -> u32 {
    let mut r = 1;
    while n >= 10 {
        n /= 10;
        r += 1;
    }
    r
}

