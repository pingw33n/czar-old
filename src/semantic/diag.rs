use crate::diag::{self, DiagRef};
use crate::hir::{Hir, NodeId, NodeMap, Span};
use crate::semantic::discover::DiscoverData;

pub type ErrorStateRef = std::rc::Rc<std::cell::RefCell<ErrorState>>;

#[derive(Default)]
pub struct ErrorState {
    /// Has fatal module-level errors.
    /// When this is becomes `true`, no more checking is performed.
    pub fatal_in_mod: bool,

    /// Has fatal function-level errors.
    /// When a fatal error reported inside function body, no more checking of that function body is
    /// done.
    pub fatal_in_fn_decls: NodeMap<()>,
}

#[derive(Clone)]
pub struct SemaDiag {
    pub diag: DiagRef,
    pub error_state: ErrorStateRef,
}

impl SemaDiag {
    pub fn has_fatal_in_mod(&self) -> bool {
        self.error_state.borrow().fatal_in_mod
    }

    pub fn has_fatal_in_fn(&self, hir: &Hir, discover_data: &DiscoverData, node: NodeId) -> bool {
        discover_data.try_fn_decl_of(node)
            .or_else(|| hir.try_fn_decl(node).map(|_| node))
            .map(|v| self.error_state.borrow().fatal_in_fn_decls.contains_key(&v))
            .unwrap_or(false)
    }

    pub fn error_span(&self,
        hir: &Hir,
        discover_data: &DiscoverData,
        node: NodeId,
        span: Span,
        text: String,
    ) {
        let id = discover_data.source_of(node, hir);

        self.diag.borrow_mut().report(diag::Report {
            severity: diag::Severity::Error,
            text,
            source: Some(diag::Source {
                id,
                span,
            })
        });
    }

    pub fn fatal_span(&self,
        hir: &Hir,
        discover_data: &DiscoverData,
        node: NodeId,
        span: Span,
        text: String,
    ) {
        let r = self.error_span(hir, discover_data, node, span, text);
        if let Some(fn_decl) = discover_data.try_fn_decl_of(node) {
            self.error_state.borrow_mut().fatal_in_fn_decls.insert(fn_decl, ());
        } else {
            self.error_state.borrow_mut().fatal_in_mod = true;
        }
        r
    }
}