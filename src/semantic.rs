pub mod check;
pub mod diag;
pub mod discover;
pub mod resolve;

use crate::hir::*;

fn fatal(span: crate::syntax::Span, s: impl std::fmt::Display) -> ! {
    panic!("[{}:{}] {}", span.start, span.end, s);
}

#[derive(Clone, Eq, Debug, Hash, PartialEq)]
pub struct FnSignature {
    items: Vec<Ident>,
}

impl FnSignature {
    pub fn empty() -> Self {
        Self {
            items: Vec::new(),
        }
    }

    pub fn from_idents(idents: &[&str]) -> Self {
        Self::from_iter(idents.iter().map(|v| *v))
    }

    pub fn from_iter<T, I>(it: I) -> Self
        where T: Into<Ident>,
              I: Iterator<Item=T>,
    {
        let mut items = Vec::new();
        for item in it {
            items.push(item.into());
        }
        Self {
            items,
        }
    }

    pub fn from_decl(node: NodeId, hir: &Hir) -> Self {
        let params = &hir.fn_decl(node).params;
        let it = params.iter()
            .map(|&param| hir.fn_decl_param(param).pub_name.value.as_ref()
                .map(|v| v.clone())
                .unwrap_or_else(|| Ident::underscore()));
        Self::from_iter(it)
    }

    pub fn from_call(node: NodeId, hir: &Hir) -> FnSignature {
        let params = &hir.fn_call(node).params;
        let it = params.iter()
            .map(|param| param.name.as_ref()
                .map(|v| v.value.clone())
                .unwrap_or_else(|| Ident::underscore()));
        Self::from_iter(it)
    }
}

impl std::fmt::Display for FnSignature {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                write!(f, ":")?;
            }
            write!(f, "{}", item.as_str())?;
        }
        write!(f, ")")
    }
}