use atomic_refcell::AtomicRefCell;
use if_chain::if_chain;
use std::collections::{HashMap, HashSet};

use crate::diag::DiagRef;
use crate::hir::*;
use crate::package::{GlobalNodeId, PackageId, Packages};
use crate::util::enums::EnumExt;
use crate::util::iter::IteratorExt;

use super::discover::{DiscoverData, NsKind, ScopeVid};

#[derive(Default)]
pub struct ResolveCache {
    inner: AtomicRefCell<ResolveCacheInner>,
}

#[derive(Default)]
struct ResolveCacheInner {
    by_node: HashMap<NodeId, Result<Resolution>>,

    /// Dedups errors in tree paths.
    /// This is needed because not all errors can be cached: e.g. items in `PathSegment`.
    errors: HashSet<(SourceId, Span)>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolutionKind {
    Exact,

    /// Nodes consist of module node to which the empty path points.
    /// Trailing path is empty.
    Empty,

    /// Nodes consist of module node to which the wildcard path points.
    /// Trailing path is empty.
    Wildcard,

    /// Nodes consist of type node starting from which type-based resolution is required.
    /// Trailing path is the path starting at the type node.
    Type,
}

#[derive(Clone, Debug, Eq, PartialEq)] // FIXME remove Clone
pub struct Resolution {
    kind: ResolutionKind,
    package_id: Option<PackageId>,
    nodes: HashSet<(NsKind, NodeId)>,
    /// See `ResolutionKind` for details.
    trailing_path: Vec<S<Ident>>,
}

impl Resolution {
    fn new(kind: ResolutionKind) -> Self {
        Self {
            kind,
            package_id: None,
            nodes: Default::default(),
            trailing_path: Default::default(),
        }
    }

    fn single(kind: ResolutionKind, ns: NsKind, target: GlobalNodeId) -> Self {
        let mut r = Self::new(kind);
        r.package_id = Some(target.0);
        r.nodes.insert((ns, target.1));
        r
    }

    fn single_type(trailing_path: Vec<S<Ident>>, target: GlobalNodeId) -> Self {
        let mut r = Self::single(ResolutionKind::Type, NsKind::Type, target);
        r.trailing_path = trailing_path;
        r
    }

    pub fn kind(&self) -> ResolutionKind {
        self.kind
    }

    pub fn package_id(&self) -> Option<PackageId> {
        self.package_id
    }

    pub fn nodes<'a>(&'a self) -> impl Iterator<Item=(NsKind, GlobalNodeId)> + 'a {
        let pkg_id = self.package_id;
        self.nodes.iter()
            .copied()
            .map(move |(k, n)| (k, (pkg_id.unwrap(), n)))
    }

    pub fn nodes_of_kind<'a>(&'a self, kind: NsKind) -> impl Iterator<Item=GlobalNodeId> + 'a {
        self.nodes()
            .filter(move |(k, _)| *k == kind)
            .map(|(_, n)| n)
    }

    fn insert_node(&mut self, kind: NsKind, node: GlobalNodeId) {
        assert_eq!(self.package_id.replace(node.0).unwrap_or(node.0), node.0);
        self.nodes.insert((kind, node.1));
    }

    fn type_or_value(&self) -> Option<GlobalNodeId> {
        self.nodes_of_kind(NsKind::Type).next()
            .or_else(|| self.nodes_of_kind(NsKind::Value).next())
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.package_id.is_none()
    }

    fn into_non_empty(self) -> Option<Self> {
        if self.is_empty() {
            None
        } else {
            Some(self)
        }
    }

    pub fn trailing_path(&self) -> &[S<Ident>] {
        &self.trailing_path
    }
}

pub type Result<T> = std::result::Result<T, ()>;

#[derive(Clone)]
pub struct Resolver<'a> {
    pub discover_data: &'a DiscoverData,
    pub hir: &'a Hir,
    pub package_id: PackageId,
    pub packages: &'a Packages,
    pub diag: DiagRef,
    pub cache: &'a ResolveCache,
}

impl Resolver<'_> {
    pub fn resolve_node(&self, path: NodeId) -> Result<Resolution> {
        self.resolve(path, &mut HashSet::new())
    }

    pub fn resolve_in_package(&self,
        path: &[&str],
    ) -> Result<Resolution> {
        let path_idents: Vec<_> = path
            .iter()
            .map(|&s| Span::empty().spanned(Some(Ident::from(s))))
            .collect();
        self.clone().resolve_path_idents(
            Resolution::new(ResolutionKind::Exact),
            self.hir.root,
            (self.hir.root, 0),
            Some(PathAnchor::Package),
            path_idents,
            &mut HashSet::new(),
        )
    }

    fn with_package(&self, package_id: PackageId) -> Self {
        if package_id == self.package_id {
            self.clone()
        } else {
            let package = &self.packages[package_id];
            Self {
                discover_data: &package.discover_data,
                hir: &package.hir,
                package_id,
                packages: self.packages,
                diag: self.diag.clone(),
                cache: package.check_data.resolve_cache(),
            }
        }
    }

    fn hir(&self, package_id: PackageId) -> &Hir {
        if package_id == self.package_id {
            self.hir
        } else {
            &self.packages[package_id].hir
        }
    }

    fn resolve(&self,
        path: NodeId,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        if let Some(r) = self.cache.inner.borrow().by_node.get(&path) {
            return r.clone();
        }
        assert!(paths.insert((self.package_id, path)));

        let (path_idents, anchor, use_) = self.prepare_path(path);
        let r = self.resolve0(path, anchor, path_idents, paths);

        if use_ {
            let existing = self.cache.inner.borrow_mut().by_node.insert(path, r.clone());
            if let Some(e) = existing {
                debug_assert_eq!(e, r);
            }
        }

        r
    }

    fn prepare_path(&self, path: NodeId) -> (Vec<S<Option<Ident>>>, Option<S<PathAnchor>>, bool) {
        let mut path_idents = Vec::new();
        let mut n = path;
        let (anchor, use_) = loop {
            let nk = self.hir.node_kind(n);
            match nk.value {
                NodeKind::Path => {
                    break (self.hir.path(n).anchor,
                        self.hir.node_kind(self.discover_data.parent_of(n)).value == NodeKind::Use);
                }
                NodeKind::PathEndIdent => {
                    let PathEndIdent { item, renamed_as: _ } = self.hir.path_end_ident(n);
                    path_idents.push(item.ident.clone().map(Some));
                }
                NodeKind::PathEndStar | NodeKind::PathEndEmpty => path_idents.push(nk.span.spanned(None)),
                NodeKind::PathSegment => {
                    let PathSegment { prefix, suffix: _ } = self.hir.path_segment(n);
                    for PathItem { ident, ty_params: _ } in prefix.iter().rev() {
                        path_idents.push(ident.clone().map(Some));
                    }
                }
                _ => unreachable!(),
            }
            n = self.discover_data.parent_of(n);
        };

        path_idents.reverse();

        (path_idents, anchor, use_)
    }

    fn resolve0(&self,
        path: NodeId,
        anchor: Option<S<PathAnchor>>,
        path_idents: Vec<S<Option<Ident>>>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        let kind = match self.hir.node_kind(path).value {
            NodeKind::PathEndIdent => ResolutionKind::Exact,
            NodeKind::PathEndStar => ResolutionKind::Wildcard,
            NodeKind::PathEndEmpty => ResolutionKind::Empty,
            _ => unreachable!(),
        };

        let reso = if let Some(anchor) = anchor {
            Resolution::single(kind, NsKind::Type, match anchor.value {
                PathAnchor::Package => (self.package_id, self.hir.root),
                PathAnchor::Root => unimplemented!(),
                PathAnchor::Super { count } => {
                    assert!(count > 0);
                    let mut scope = path;
                    for _ in 0..=count {
                        scope = if let Some(scope) = self.discover_data.try_module_of(scope) {
                            scope
                        } else {
                            self.error(path, anchor.span,
                                "can't resolve path: too many leading `super` keywords".into());
                            return Err(());
                        };
                    }
                    (self.package_id, scope)
                }
            })
        } else {
            let scope = self.discover_data.def_scope_of(path);
            let first = path_idents.first().unwrap().clone().map(|v| v.unwrap());
            let first = first.as_ref().map(|v| v.as_str());
            let reso = self.resolve_in_scopes(kind, path, scope, first, paths)?;
            if !reso.is_empty() {
                reso
            } else if let Some(package) = self.packages.try_by_name(&first.value) {
                Resolution::single(kind, NsKind::Type, (package.id, package.hir.root))
            } else {
                let std_resolver = self.with_package(PackageId::std());
                // TODO cache this
                let std_prelude = std_resolver
                    .resolve_in_package(&["prelude"])?
                    .nodes_of_kind(NsKind::Type)
                    .exactly_one()
                    .unwrap();
                if_chain! {
                    if !paths.contains(&std_prelude);
                    let reso = std_resolver.resolve_in_scope(kind, path, (std_prelude.1, 0), first, paths)?;
                    if !reso.is_empty();
                    then {
                        reso
                    } else {
                        self.error(path, first.span, format!(
                            "could not find `{}` in current scope", first.value));
                        return Err(());
                    }
                }
            }
        };

        let anchor = anchor.map(|v| v.value);
        let more = path_idents.len() > if anchor.is_some() { 0 } else { 1 };
        let reso = if more {
            let (pkg, scope) = reso.type_or_value().unwrap();
            self.with_package(pkg)
                .resolve_path_idents(reso, path, (scope, 0), anchor, path_idents, paths)?
        } else {
            reso
        };

        assert!(!reso.is_empty());
        assert!(reso.kind == kind ||
            reso.kind == ResolutionKind::Type && kind == ResolutionKind::Exact);

        Ok(reso)
    }

    fn resolve_path_idents(mut self,
        mut reso: Resolution,
        node: NodeId, // For error reporting
        mut scope: ScopeVid,
        anchor: Option<PathAnchor>,
        idents: Vec<S<Option<Ident>>>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        let start = if anchor.is_some() { 0 } else { 1 };
        for (i, ident) in idents.iter().enumerate().skip(start) {
            let scope_kind = self.hir.node_kind(scope.0).value;
            let type_reso = matches!(scope_kind, NodeKind::Struct | NodeKind::TypeAlias);

            // The scope must be a module if at least one is true:
            // 1. We are resolving wildcard or empty path.
            // 2. We didn't detect a type resolution condition.
            if (matches!(reso.kind, ResolutionKind::Wildcard | ResolutionKind::Empty) || !type_reso)
                && scope_kind != NodeKind::Module
            {
                self.error(node, idents[i - 1].span, "expected module".into());
                return Err(());
            }

            let ident = if let Some(v) = ident.value.clone() {
                ident.span.spanned(v)
            } else {
                assert_eq!(i, idents.len() - 1);
                assert!(matches!(reso.kind, ResolutionKind::Wildcard | ResolutionKind::Empty));
                break;
            };

            if type_reso {
                reso = Resolution::single_type(idents
                    .into_iter()
                    .skip(i - 1)
                    .map(|v| v.map(|v| v.unwrap()))
                    .collect(),
                    (self.package_id, scope.0));
                break;
            } else if ident.value.is_self_lower() {
                assert_eq!(i, idents.len() - 1);
                reso = Resolution::single(reso.kind, NsKind::Type, (self.package_id, scope.0));
                break;
            }
            reso = self.resolve_in_scope(
                reso.kind,
                node,
                scope,
                ident.as_ref().map(|v| v.as_str()),
                paths,
            )?;

            if let Some((pkg, sc)) = reso.type_or_value() {
                self = self.with_package(pkg);
                scope = (sc, 0);
            } else {
                let s = if i == 0 {
                    match anchor.unwrap() {
                        PathAnchor::Package => "package root",
                        PathAnchor::Root => "root",
                        PathAnchor::Super { .. } => "parent module",
                    }.into()
                } else {
                    format!("`{}`", idents[i - 1].value.as_ref().unwrap())
                };
                self.error(node, ident.span, format!(
                    "could not find `{}` in {}", ident.value, s));
                return Err(());
            }
        }
        assert!(!reso.is_empty());
        Ok(reso)
    }

    fn resolve_in_scopes(&self,
        kind: ResolutionKind,
        node: NodeId, // for error reporting
        mut scope: ScopeVid,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        loop {
            if let Some(r) = self.resolve_in_scope(kind, node, scope, name, paths)?.into_non_empty() {
                break Ok(r);
            }
            if self.hir.node_kind(scope.0).value == NodeKind::Module {
                break Ok(Resolution::new(kind));
            }
            scope = if let Some(v) = self.discover_data.try_parent_scope_of(scope.0) {
                v
            } else {
                break Ok(Resolution::new(kind));
            };
        }
    }

    fn resolve_in_scope(&self,
        kind: ResolutionKind,
        node: NodeId, // for error reporting
        scope: ScopeVid,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        let mut r = Resolution::new(kind);
        for ns_kind in NsKind::iter() {
            if let Some(scope_) = self.discover_data.try_scope(scope.0, ns_kind) {
                let mut nodes = scope_.get(name.value, scope.1).enumerate();
                while let Some((i, node)) = nodes.next() {
                    if paths.contains(&(self.package_id, node)) {
                        break;
                    }
                    if self.hir.node_kind(node).value == NodeKind::PathEndIdent {
                        assert_eq!(i, 0);
                        assert!(nodes.next().is_none());
                        let indirect = self.resolve(node, paths)?;
                        for node in indirect.nodes_of_kind(ns_kind) {
                            r.insert_node(ns_kind, node);
                        }
                        break;
                    } else {
                        r.insert_node(ns_kind, (self.package_id, node));
                    }
                }
            } else {
                return Ok(r);
            }
        }
        if !r.is_empty() {
            return Ok(r);
        }
        let scope_ = self.discover_data.scope(scope.0, NsKind::Type);
        if !scope_.wildcard_imports().is_empty() {
            let mut found_in_wc_imports = Vec::new();
            for &path in scope_.wildcard_imports() {
                if paths.contains(&(self.package_id, path)) {
                    continue;
                }
                if let Some((pkg, scope)) = self.resolve(path, paths)?.type_or_value() {
                    let r = self.with_package(pkg)
                        .resolve_in_scope(kind, node, (scope, 0), name, paths)?;
                    if !r.is_empty() {
                        found_in_wc_imports.push(r);
                    }
                }
            }
            match found_in_wc_imports.len() {
                0 => {}
                1 => return Ok(found_in_wc_imports[0].clone()),
                _ => {
                    self.error(node, name.span, format!(
                        "`{}` found in multiple wildcard imports", name.value));
                    return Err(());
                },
            }
        }
        Ok(Resolution::new(kind))
    }

    fn error(&self, node: NodeId, span: Span, text: String) {
        let source_id = self.discover_data.source_of(node, self.hir);
        if self.cache.inner.borrow_mut().errors.insert((source_id, span)) {
            self.diag.borrow_mut().error_span(self.hir, self.discover_data, node, span, text);
        }
    }
}