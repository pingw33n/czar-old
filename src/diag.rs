use std::fmt::{Result, Write};

use crate::hir::{SourceId, Sources};
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

    pub fn print(&self, mut out: impl Write, sources: &Sources) -> Result {
        for (i, Report { severity, text, source }) in self.reports.iter().enumerate() {
            if i > 0 {
                writeln!(out)?;
            }
            let severity = match severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            writeln!(out, "{}: {}", severity, text)?;
            if let Some(Source { id, span }) = source {
                let source = &sources[*id];
                writeln!(out, "  --> {}:{}:{}", source.path.to_string_lossy(), span.start, span.end)?;
            }
        }
        Ok(())
    }
}