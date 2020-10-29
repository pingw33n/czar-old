pub mod check;
pub mod discover;
pub mod resolve;

use crate::hir::*;

#[derive(Clone, Eq, Debug, Hash, PartialEq)]
pub struct FnParamsSignature {
    labels: Vec<Ident>,
}

impl FnParamsSignature {
    pub fn empty() -> Self {
        Self {
            labels: Vec::new(),
        }
    }

    pub fn from_idents(idents: &[&str]) -> Self {
        Self::from_iter(idents.iter().map(|v| *v))
    }

    pub fn from_iter<T, I>(it: I) -> Self
        where T: Into<Ident>,
              I: Iterator<Item=T>,
    {
        let mut labels = Vec::new();
        for l in it {
            labels.push(l.into());
        }
        Self {
            labels,
        }
    }

    pub fn from_def(node: NodeId, hir: &Hir) -> Self {
        let params = &hir.fn_def(node).params;
        let it = params.iter()
            .map(|&param| hir.fn_def_param(param).label.value.as_ref()
                .map(|v| v.clone())
                .unwrap_or_else(|| Ident::underscore()));
        Self::from_iter(it)
    }

    pub fn from_call(node: NodeId, hir: &Hir) -> FnParamsSignature {
        let params = &hir.fn_call(node).params;
        let it = params.iter()
            .map(|param| param.name.as_ref()
                .map(|v| v.value.clone())
                .unwrap_or_else(|| Ident::underscore()));
        Self::from_iter(it)
    }
}

impl std::fmt::Display for FnParamsSignature {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, item) in self.labels.iter().enumerate() {
            if i > 0 {
                write!(f, ":")?;
            }
            write!(f, "{}", item.as_str())?;
        }
        write!(f, ")")
    }
}