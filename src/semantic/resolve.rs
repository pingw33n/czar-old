use atomic_refcell::AtomicRefCell;
use enum_map::EnumMap;
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
    resolutions: HashMap<NodeId, Result<Resolution>>,

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Resolution {
    kind: ResolutionKind,
    nodes: HashSet<(NsKind, GlobalNodeId)>,
    /// See `ResolutionKind` for details.
    trailing_path: Vec<S<Ident>>,
}

impl Resolution {
    fn new(kind: ResolutionKind) -> Self {
        Self {
            kind,
            nodes: Default::default(),
            trailing_path: Default::default(),
        }
    }

    pub fn kind(&self) -> ResolutionKind {
        self.kind
    }

    pub fn nodes<'a>(&'a self) -> impl Iterator<Item=(NsKind, GlobalNodeId)> + 'a {
        self.nodes.iter().copied()
    }

    pub fn ns_nodes<'a>(&'a self, ns: NsKind) -> impl Iterator<Item=GlobalNodeId> + 'a {
        self.nodes()
            .filter(move |(k, _)| *k == ns)
            .map(|(_, n)| n)
    }

    fn insert_node(&mut self, ns: NsKind, node: GlobalNodeId) {
        debug_assert!(!self.nodes().any(|(_, n)| n == node));
        self.nodes.insert((ns, node));
    }

    fn type_or_value(&self) -> Option<GlobalNodeId> {
        self.ns_nodes(NsKind::Type).next()
            .or_else(|| self.ns_nodes(NsKind::Value).next())
    }

    fn clear(&mut self) {
        self.nodes.clear();
        self.trailing_path.clear();
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
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
        let mut reso = Resolution::new(ResolutionKind::Exact);
        self.clone().resolve_path_idents(
            &mut reso,
            self.hir.root,
            (self.hir.root, 0),
            Some(PathAnchor::Package),
            path_idents,
            &mut HashSet::new(),
        )?;
        Ok(reso)
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

    fn reso_kind(&self, path: NodeId) -> ResolutionKind {
        match self.hir.node_kind(path).value {
            NodeKind::PathEndIdent => ResolutionKind::Exact,
            NodeKind::PathEndStar => ResolutionKind::Wildcard,
            NodeKind::PathEndEmpty => ResolutionKind::Empty,
            _ => unreachable!(),
        }
    }

    fn resolve(&self,
        path: NodeId,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        if let Some(r) = self.cache.inner.borrow().resolutions.get(&path) {
            return r.clone();
        }

        let mut reso = Resolution::new(self.reso_kind(path));

        if !paths.insert((self.package_id, path)) {
            return Ok(reso);
        }

        let (path_idents, anchor, use_) = self.prepare_path(path);
        let r = self.resolve0(&mut reso, path, anchor, path_idents, paths);

        assert!(paths.remove(&(self.package_id, path)));

        if use_ {
            assert!(self.cache.inner.borrow_mut().resolutions.insert(path, r.map(|_| reso.clone())).is_none());
        }

        r?;

        Ok(reso)
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
        reso: &mut Resolution,
        path: NodeId,
        anchor: Option<S<PathAnchor>>,
        path_idents: Vec<S<Option<Ident>>>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        let initial_kind = reso.kind();
        assert!(reso.is_empty());
        if let Some(anchor) = anchor {
            let node = match anchor.value {
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
            };
            reso.insert_node(NsKind::Type, node);
        } else {
            let scope = self.discover_data.def_scope_of(path);
            let first = path_idents.first().unwrap().clone().map(|v| v.unwrap());
            let first = first.as_ref().map(|v| v.as_str());
            self.resolve_in_scope_tree(reso, path, scope, first, paths)?;
            if !reso.is_empty() {
            } else if let Some(package) = self.packages.try_by_name(&first.value) {
                reso.insert_node(NsKind::Type, (package.id, package.hir.root));
            } else {
                let std_resolver = self.with_package(PackageId::std());
                // TODO cache this
                let std_prelude = std_resolver
                    .resolve_in_package(&["prelude"])?
                    .ns_nodes(NsKind::Type)
                    .exactly_one()
                    .unwrap();
                std_resolver.resolve_in_scope(reso, path, (std_prelude.1, 0), first, paths)?;
                if reso.is_empty() {
                    self.error(path, first.span, format!(
                        "could not find `{}` in current scope", first.value));
                    return Err(());
                }
            }
        }
        assert!(!reso.is_empty());

        let anchor = anchor.map(|v| v.value);
        let more = path_idents.len() > if anchor.is_some() { 0 } else { 1 };
        if more {
            let (pkg, scope) = reso.type_or_value().unwrap();
            self.with_package(pkg)
                .resolve_path_idents(reso, path, (scope, 0), anchor, path_idents, paths)?
        }

        assert!(!reso.is_empty());
        assert!(reso.kind() == initial_kind ||
            reso.kind() == ResolutionKind::Type && initial_kind == ResolutionKind::Exact);

        Ok(())
    }

    fn resolve_path_idents(mut self,
        reso: &mut Resolution,
        node: NodeId, // For error reporting
        mut scope: ScopeVid,
        anchor: Option<PathAnchor>,
        idents: Vec<S<Option<Ident>>>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
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

            reso.clear();

            if type_reso {
                reso.insert_node(NsKind::Type, (self.package_id, scope.0));
                reso.kind = ResolutionKind::Type;
                reso.trailing_path = idents
                    .into_iter()
                    .skip(i - 1)
                    .map(|v| v.map(|v| v.unwrap()))
                    .collect();
                break;
            } else if ident.value.is_self_lower() {
                assert_eq!(i, idents.len() - 1);
                reso.insert_node(NsKind::Type, (self.package_id, scope.0));
                break;
            }
            self.resolve_in_scope(
                reso,
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
        Ok(())
    }

    fn resolve_in_scope_tree(&self,
        reso: &mut Resolution,
        node: NodeId, // for error reporting
        mut scope: ScopeVid,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        assert!(reso.is_empty());
        loop {
            self.resolve_in_scope(reso, node, scope, name, paths)?;
            if !reso.is_empty() {
                break;
            }
            if self.hir.node_kind(scope.0).value == NodeKind::Module {
                break;
            }
            scope = if let Some(v) = self.discover_data.try_parent_scope_of(scope.0) {
                v
            } else {
                break;
            };
        }
        Ok(())
    }

    fn resolve_in_scope(&self,
        reso: &mut Resolution,
        node: NodeId, // for error reporting
        scope_vid: ScopeVid,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<()> {
        if let Some(scope) = self.discover_data.try_scope(scope_vid.0) {
            // 1. Look in namespaces of the scope.
            for ns in NsKind::iter() {
                for node in scope.namespace(ns).get(name.value, scope_vid.1) {
                    reso.insert_node(ns, (self.package_id, node));
                }
            }

            // 2. Look in non-wildcard imports.
            if let Some(path) = scope.try_import(name.value) {
                let target = self.resolve(path, paths)?;
                let mut ns_ok = EnumMap::<NsKind, bool>::new();
                for (ns, node) in target.nodes() {
                    if ns_ok[ns] || reso.ns_nodes(ns).next().is_none() {
                        ns_ok[ns] = true;
                        reso.insert_node(ns, node);
                    }
                }
            }

            // 3. Look in wildcard imports if nothing found.
            if reso.is_empty() {
                let mut found_in_wc_imports = Vec::new();
                for &path in scope.wildcard_imports() {
                    if let Some((pkg, scope)) = self.resolve(path, paths)?.type_or_value() {
                        let mut wild_reso = Resolution::new(ResolutionKind::Exact);
                        self.with_package(pkg)
                            .resolve_in_scope(&mut wild_reso, node, (scope, 0), name, paths)?;
                        if !wild_reso.is_empty() {
                            found_in_wc_imports.push(wild_reso);
                        }
                    }
                }
                match found_in_wc_imports.len() {
                    0 => {}
                    1 => {
                        let mut inserted = 0;
                        for (ns, node) in found_in_wc_imports[0].nodes() {
                            if reso.ns_nodes(ns).next().is_none() {
                                reso.insert_node(ns, node);
                                inserted += 1;
                            }
                        }
                        assert!(inserted > 0);
                    }
                    _ => {
                        self.error(node, name.span, format!(
                            "`{}` found in multiple wildcard imports", name.value));
                        return Err(());
                    },
                }
            }
        }
        Ok(())
    }

    fn error(&self, node: NodeId, span: Span, text: String) {
        let source_id = self.discover_data.source_of(node, self.hir);
        if self.cache.inner.borrow_mut().errors.insert((source_id, span)) {
            self.diag.borrow_mut().error_span(self.hir, self.discover_data, node, span, text);
        }
    }
}