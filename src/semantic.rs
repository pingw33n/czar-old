pub mod check;
pub mod discover;
pub mod resolve;

use crate::hir::{self, *};
use crate::semantic::discover::DiscoverData;

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

    pub fn from_def(fn_def: NodeId /*FnDef*/, hir: &Hir) -> Self {
        let params = &hir.fn_def(fn_def).params;
        let it = params.iter()
            .map(|&param| hir.fn_def_param(param).label.value.as_ref()
                .map(|v| v.clone())
                .unwrap_or_else(|| Ident::underscore()));
        Self::from_iter(it)
    }

    pub fn from_call(fn_call: NodeId /*FnCall*/, hir: &Hir) -> FnParamsSignature {
        let args = &hir.fn_call(fn_call).args;
        let it = args.iter()
            .map(|arg| arg.name.as_ref()
                .map(|v| v.value.clone())
                .unwrap_or_else(|| Ident::underscore()));
        Self::from_iter(it)
    }

    pub fn display_with_name<'a>(&'a self, name: &'a str) -> impl std::fmt::Display + 'a {
        struct Impl<'a> {
            name: &'a str,
            sign: &'a FnParamsSignature,
        }
        impl std::fmt::Display for Impl<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}::{}", self.name, self.sign)
            }
        }
        Impl {
            name,
            sign: self,
        }
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

#[derive(Clone, Debug)]
pub struct PathItem {
    pub node: NodeId /*PathSegment|PathEndIdent*/,
    pub name: S<Ident>,
    pub ty_args: Option<S<Vec<NodeId /*TyExpr*/>>>,
}

impl PathItem {
    pub fn from_hir(node: NodeId, item: &hir::PathItem) -> Self {
        Self {
            node,
            name: item.ident.clone(),
            ty_args: item.ty_args.clone(),
        }
    }

    pub fn from_hir_path_end(
        path: NodeId /*Path|PathSegment|PathEndIdent|PathEndStar|PathEndEmpty*/,
        hir: &Hir,
        discover_data: &DiscoverData,
    ) -> Vec<Self> {
        let mut r = Vec::new();
        let mut n = path;
        loop {
            let nk = hir.node_kind(n);
            match nk.value {
                NodeKind::Path => {
                    break;
                }
                NodeKind::PathEndIdent => {
                    r.push(PathItem::from_hir(n, &hir.path_end_ident(n).item));
                }
                NodeKind::PathSegment => {
                    let PathSegment { prefix, suffix: _ } = hir.path_segment(n);
                    for item in prefix.iter().rev() {
                        r.push(PathItem::from_hir(n, item));
                    }
                }
                NodeKind::PathEndStar | NodeKind::PathEndEmpty => {}
                _ => unreachable!(),
            }
            n = discover_data.parent_of(n).0;
        };
        r.reverse();
        r
    }

    pub fn from_hir_path_start(
        path: NodeId /*Path*/,
        hir: &Hir,
        discover_data: &DiscoverData,
    ) -> Vec<Self> {
        Self::from_hir_path_end(hir.find_flat_path_end(path), hir, discover_data)
    }
}