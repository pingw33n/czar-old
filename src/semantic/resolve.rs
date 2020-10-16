use if_chain::if_chain;
use std::collections::HashSet;

use crate::hir::*;
use crate::hir::traverse::*;
use crate::package::{GlobalNodeId, PackageId, PackageKind, Packages};
use crate::util::enums::EnumExt;
use crate::util::iter::IteratorExt;

use super::*;
use super::diag::SemaDiag;
use super::discover::{DiscoverData, NsKind, ScopeItem};

#[derive(Debug, Default)]
pub struct ResolveData {
    path_to_resolution: NodeMap<Resolution>,
    entry_point: Option<NodeId>,
}

impl ResolveData {
    pub fn build(
        discover_data: &DiscoverData,
        hir: &Hir,
        package_id: PackageId,
        package_name: &Ident,
        package_kind: PackageKind,
        packages: &Packages,
        diag: SemaDiag,
    ) -> Self {
        let mut resolve_data = ResolveData::default();
        hir.traverse(&mut Build {
            discover_data,
            resolve_data: &mut resolve_data,
            package_id,
            packages,
            diag: diag.clone(),
        });

        // Resolve `main::()`, even if there are errors.
        if package_kind == PackageKind::Exe {
            let resolver = Resolver {
                discover_data,
                resolve_data: &resolve_data,
                hir,
                package_id,
                packages,
                diag: diag.clone(),
            };
            if let Ok(reso) = resolver.resolve_in_package(&["main"]) {
                let node = reso.nodes_of_kind(NsKind::Value)
                    .filter(|n| n.0 == package_id)
                    .filter(|n| discover_data.fn_decl_signature(n.1) == &FnSignature::empty())
                    .next()
                    .map(|n| n.1);
                if let Some(node) = node {
                    resolve_data.entry_point = Some(node);
                } else {
                    diag.error_span(hir, discover_data, hir.root, Span::empty(), format!(
                        "`main::()` function not found in package `{}`", package_name));
                }
            }
        }

        resolve_data
    }

    fn insert(&mut self, node: NodeId, resolution: Resolution) {
        assert!(self.path_to_resolution.insert(node, resolution).is_none());
    }

    pub fn resolution_of(&self, path: NodeId) -> &Resolution {
        &self.path_to_resolution[&path]
    }

    pub fn try_resolution_of(&self, path: NodeId) -> Option<&Resolution> {
        self.path_to_resolution.get(&path)
    }

    pub fn entry_point(&self) -> Option<NodeId> {
        self.entry_point
    }
}

struct Build<'a> {
    discover_data: &'a DiscoverData,
    resolve_data: &'a mut ResolveData,
    package_id: PackageId,
    packages: &'a Packages,
    diag: SemaDiag,
}

impl HirVisitor for Build<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        match ctx.kind {
            NodeKind::PathEndIdent | NodeKind::PathEndStar => {
                let target = Resolver {
                    discover_data: self.discover_data,
                    resolve_data: self.resolve_data,
                    hir: ctx.hir,
                    package_id: self.package_id,
                    packages: self.packages,
                    diag: self.diag.clone(),
                }.resolve_node(ctx.node);
                if let Ok(target) = target {
                    self.resolve_data.insert(ctx.node, target);
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug, Default)] // FIXME remove Clone
pub struct Resolution {
    package_id: Option<PackageId>,
    nodes: HashSet<(NsKind, NodeId)>,
}

impl Resolution {
    pub fn single(kind: NsKind, target: GlobalNodeId) -> Self {
        let mut r = Self::default();
        r.package_id = Some(target.0);
        r.nodes.insert((kind, target.1));
        r
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

    pub fn insert_node(&mut self, kind: NsKind, node: GlobalNodeId) {
        assert_eq!(self.package_id.replace(node.0).unwrap_or(node.0), node.0);
        self.nodes.insert((kind, node.1));
    }

    fn type_or_value(&self) -> Option<GlobalNodeId> {
        self.nodes_of_kind(NsKind::Type).next()
            .or_else(|| self.nodes_of_kind(NsKind::Value).next())
    }

    pub fn is_empty(&self) -> bool {
        self.package_id.is_none()
    }

    pub fn into_non_empty(self) -> Option<Self> {
        if self.is_empty() {
            None
        } else {
            Some(self)
        }
    }
}

#[derive(Debug)]
pub struct ResolveError(());

pub type Result<T> = std::result::Result<T, ResolveError>;

#[derive(Clone)]
pub struct Resolver<'a> {
    pub discover_data: &'a DiscoverData,
    pub resolve_data: &'a ResolveData,
    pub hir: &'a Hir,
    pub package_id: PackageId,
    pub packages: &'a Packages,
    pub diag: SemaDiag,
}

impl<'a> Resolver<'a> {
    pub fn resolve_node(&self, path: NodeId) -> Result<Resolution> {
        self.resolve(path, &mut HashSet::new())
    }

    pub fn resolve_in_package(&self,
        path: &[&str],
    ) -> Result<Resolution> {
        let path_idents: Vec<_> = path
            .iter()
            .map(|&s| Span::empty().spanned(Ident::from(s)))
            .collect();
        self.clone().resolve_path_idents(
            self.hir.root,
            self.hir.root,
            Some(PathAnchor::Package),
            &path_idents,
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
                resolve_data: &package.resolve_data,
                hir: &package.hir,
                package_id,
                packages: self.packages,
                diag: self.diag.clone(),
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
        if let Some(r) = self.resolve_data.try_resolution_of(path) {
            return Ok(r.clone());
        }

        assert!(paths.insert((self.package_id, path)));

        let mut path_idents = Vec::new();
        let mut n = path;
        let anchor = loop {
            match self.hir.node_kind(n).value {
                NodeKind::Path => {
                    break self.hir.path(n).anchor;
                }
                NodeKind::PathEndIdent => {
                    let PathEndIdent { item, renamed_as: _ } = self.hir.path_end_ident(n);
                    path_idents.push(item.ident.clone());
                }
                NodeKind::PathEndStar | NodeKind::PathEndEmpty => {}
                NodeKind::PathSegment => {
                    let PathSegment { prefix, suffix: _ } = self.hir.path_segment(n);
                    for PathItem { ident, ty_params: _ } in prefix.iter().rev() {
                        path_idents.push(ident.clone());
                    }
                }
                _ => unreachable!(),
            }
            n = self.discover_data.parent_of(n);
        };

        path_idents.reverse();

        let reso = if let Some(anchor) = anchor {
            Resolution::single(NsKind::Type, match anchor.value {
                PathAnchor::Package => (self.package_id, self.hir.root),
                PathAnchor::Root => unimplemented!(),
                PathAnchor::Super { count } => {
                    assert!(count > 0);
                    let mut scope = path;
                    for _ in 0..=count {
                        scope = if let Some(scope) = self.discover_data.try_module_of(scope) {
                            scope
                        } else {
                            return self.error(path, anchor.span,
                                "can't resolve path: too many leading `super` keywords".into());
                        };
                    }
                    (self.package_id, scope)
                }
            })
        } else {
            let scope = self.discover_data.scope_of(path);
            let first = path_idents.first().unwrap();
            let first = first.as_ref().map(|v| v.as_str());
            let reso = self.resolve_in_scopes(path, scope, first, paths)?;
            if !reso.is_empty() {
                reso
            } else if let Some(package) = self.packages.try_by_name(&first.value) {
                Resolution::single(NsKind::Type, (package.id, package.hir.root))
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
                    let reso = std_resolver.resolve_in_scope(path, std_prelude.1, first, paths)?;
                    if !reso.is_empty();
                    then {
                        reso
                    } else {
                        return self.error(path, first.span, format!(
                            "could not find `{}` in current scope", first.value));
                    }
                }
            }
        };

        let anchor = anchor.map(|v| v.value);
        let more = path_idents.len() > if anchor.is_some() { 0 } else { 1 };
        let reso = if more {
            let (pkg, scope) = reso.type_or_value().unwrap();
            self.with_package(pkg)
                .resolve_path_idents(path, scope, anchor, &path_idents, paths)?
        } else {
            reso
        };

        assert!(!reso.is_empty());

        // TODO cache result.

        Ok(reso)
    }

    fn resolve_path_idents(mut self,
        node: NodeId, // For error reporting
        mut scope: NodeId,
        anchor: Option<PathAnchor>,
        path_idents: &[S<Ident>],
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        let mut r = Resolution::default();
        let start = if anchor.is_some() { 0 } else { 1 };
        for (i, ident) in path_idents.iter().enumerate().skip(start) {
            r = if ident.value.is_self_lower() {
                    assert_eq!(i, path_idents.len() - 1);
                    Resolution::single(NsKind::Type, (self.package_id, scope))
                } else {
                    self.resolve_in_scope(
                        node,
                        scope,
                        ident.as_ref().map(|v| v.as_str()),
                        paths,
                    )?
                };
            if let Some((pkg, sc)) = r.type_or_value() {
                self = self.with_package(pkg);
                scope = sc;
            } else {
                let s = if i == 0 {
                    match anchor.unwrap() {
                        PathAnchor::Package => "package root",
                        PathAnchor::Root => "root",
                        PathAnchor::Super { .. } => "parent module",
                    }.into()
                } else {
                    format!("`{}`", path_idents[i - 1].value.as_str())
                };
                return self.error(node, ident.span, format!(
                    "could not find `{}` in {}", ident.value, s));
            }
        }
        assert!(!r.is_empty());
        Ok(r)
    }

    fn resolve_in_scopes(&self,
        node: NodeId, // for error reporting
        mut scope: NodeId,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        loop {
            if let Some(r) = self.resolve_in_scope(node, scope, name, paths)?.into_non_empty() {
                break Ok(r);
            }
            if self.hir.node_kind(scope).value == NodeKind::Module {
                break Ok(Resolution::default());
            }
            scope = if let Some(v) = self.discover_data.try_parent_scope_of(scope) {
                v
            } else {
                break Ok(Resolution::default());
            };
        }
    }

    fn resolve_in_scope(&self,
        node: NodeId, // for error reporting
        scope: NodeId,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Result<Resolution> {
        let mut r = Resolution::default();
        for ns_kind in NsKind::iter() {
            if let Some(scope_) = self.discover_data.try_scope(scope, ns_kind) {
                match scope_.try_get(name.value) {
                    Some(&ScopeItem::Single { node, .. }) => {
                        if paths.contains(&(self.package_id, node)) {
                            break;
                        }
                        if self.hir.node_kind(node).value == NodeKind::PathEndIdent {
                            return self.resolve(node, paths);
                        } else {
                            r.insert_node(ns_kind, (self.package_id, node));
                        }
                    },
                    Some(ScopeItem::Fns(fns)) => {
                        assert_eq!(ns_kind, NsKind::Value);
                        for fn_ in fns {
                            r.insert_node(ns_kind, (self.package_id, fn_.node));
                        }
                    },
                    None => {}
                }

            } else {
                return Ok(r);
            }
        }
        if !r.is_empty() {
            return Ok(r);
        }
        let scope_ = self.discover_data.scope(scope, NsKind::Type);
        if !scope_.wildcard_imports().is_empty() {
            let mut found_in_wc_imports = Vec::new();
            for &path in scope_.wildcard_imports() {
                if paths.contains(&(self.package_id, path)) {
                    continue;
                }
                if let Some((pkg, scope)) = self.resolve(path, paths)?.type_or_value() {
                    let r = self.with_package(pkg)
                        .resolve_in_scope(node, scope, name, paths)?;
                    if !r.is_empty() {
                        found_in_wc_imports.push(r);
                    }
                }
            }
            match found_in_wc_imports.len() {
                0 => {}
                1 => return Ok(found_in_wc_imports[0].clone()),
                _ => return self.error(node, name.span, format!(
                    "`{}` found in multiple wildcard imports", name.value)),
            }
        }
        Ok(Resolution::default())
    }

    fn error<T>(&self, node: NodeId, span: Span, text: String) -> Result<T> {
        self.diag.fatal_span(self.hir, self.discover_data, node, span, text);
        return Err(ResolveError(()));
    }
}