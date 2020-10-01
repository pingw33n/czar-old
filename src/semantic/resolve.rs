use enum_map::EnumMap;
use if_chain::if_chain;
use std::collections::HashSet;

use crate::hir::*;
use crate::hir::traverse::*;
use crate::package::{GlobalNodeId, PackageId, PackageKind, Packages};
use crate::util::enums::EnumExt;

use super::*;
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
        package_kind: PackageKind,
        packages: &Packages,
    ) -> Self {
        let mut resolve_data = ResolveData::default();
        hir.traverse(&mut Build {
            discover_data,
            resolve_data: &mut resolve_data,
            package_id,
            packages,
            fn_calls: Vec::new(),
        });
        if package_kind == PackageKind::Exe {
            let resolver = Resolver {
                discover_data,
                resolve_data: &resolve_data,
                hir,
                package_id,
                packages,
            };
            let reso = resolver.resolve_in_package(&["main"], Some(&FnArgsKey::from_idents(&[])));
            let node = reso.type_or_other().unwrap();
            if node.0 != package_id {
                let span = packages[node.0].hir.node_kind(node.1).span;
                fatal(span, "`main` function must be defined in the same package");
            }
            resolve_data.entry_point = Some(node.1);
        }
        resolve_data
    }

    pub fn insert(&mut self, node: NodeId, resolution: Resolution) {
        assert!(self.path_to_resolution.insert(node, resolution).is_none());
    }

    pub fn resolution_of(&self, path: NodeId) -> Resolution {
        self.path_to_resolution[&path]
    }

    pub fn try_resolution_of(&self, path: NodeId) -> Option<Resolution> {
        self.path_to_resolution.get(&path).copied()
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
    fn_calls: Vec<NodeId>,
}

impl HirVisitor for Build<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        match ctx.kind {
            NodeKind::FnCall => {
                self.fn_calls.push(ctx.node);
            }
            NodeKind::PathEndIdent | NodeKind::PathEndStar => {
                let target = Resolver {
                    discover_data: self.discover_data,
                    resolve_data: self.resolve_data,
                    hir: ctx.hir,
                    package_id: self.package_id,
                    packages: self.packages,
                }.resolve_node(ctx.node);
                if ctx.kind == NodeKind::PathEndStar
                    && target.package_id().map(|v| v != self.package_id).unwrap_or(false)
                {
                    fatal(ctx.hir.node_kind(ctx.node).span,
                        "wildcard imports can only reference symbols from the same package")
                }
                self.resolve_data.insert(ctx.node, target);
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        match ctx.kind {
            NodeKind::FnCall => {
                assert_eq!(self.fn_calls.pop().unwrap(), ctx.node);
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Resolution {
    package_id: Option<PackageId>,
    nodes: EnumMap<NsKind, Option<NodeId>>,
}

impl Resolution {
    pub fn single(kind: NsKind, target: GlobalNodeId) -> Self {
        let mut r = Self::default();
        r.package_id = Some(target.0);
        r.nodes[kind] = Some(target.1);
        r
    }

    pub fn package_id(self) -> Option<PackageId> {
        self.package_id
    }

    pub fn local_node(self, kind: NsKind) -> Option<NodeId> {
        self.nodes[kind]
    }

    pub fn node(self, kind: NsKind) -> Option<GlobalNodeId> {
        self.nodes[kind].map(|n| (self.package_id.unwrap(), n))
    }

    pub fn set_node(&mut self, kind: NsKind, node: GlobalNodeId) {
        assert_eq!(self.package_id.replace(node.0).unwrap_or(node.0), node.0);
        self.nodes[kind] = Some(node.1);
    }

    pub fn type_or_other(self) -> Option<GlobalNodeId> {
        self.type_or_other_kind().map(|k| self.node(k).unwrap())
    }

    pub fn type_or_other_kind(self) -> Option<NsKind> {
        if self.nodes[NsKind::Type].is_some() {
            return Some(NsKind::Type);
        }
        for kind in NsKind::iter() {
            if self.nodes[kind].is_some() {
                return Some(kind);
            }
        }
        None
    }

    pub fn is_empty(self) -> bool {
        self.package_id.is_none()
    }

    pub fn non_empty(self) -> Option<Self> {
        if self.is_empty() {
            None
        } else {
            Some(self)
        }
    }
}

#[derive(Clone)]
pub struct Resolver<'a> {
    pub discover_data: &'a DiscoverData,
    pub resolve_data: &'a ResolveData,
    pub hir: &'a Hir,
    pub package_id: PackageId,
    pub packages: &'a Packages,
}

impl<'a> Resolver<'a> {
    pub fn resolve_node(&self, path: NodeId) -> Resolution {
        self.resolve(path, &mut HashSet::new())
    }

    pub fn resolve_in_package(&self,
        path: &[&str],
        fn_args_key: Option<&FnArgsKey>,
    ) -> Resolution {
        let path_idents: Vec<_> = path
            .iter()
            .map(|&s| Span::new(0, 0).spanned(Ident::from(s)))
            .collect();
        self.clone().resolve_path_idents(
            self.hir.root,
            Some(PathAnchor::Package),
            &path_idents,
            fn_args_key,
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
    ) -> Resolution {
        if let Some(r) = self.resolve_data.try_resolution_of(path) {
            return r;
        }

        assert!(paths.insert((self.package_id, path)));

        let mut path_idents = Vec::new();
        let mut path_node = match self.hir.node_kind(path).value {
            NodeKind::PathEndIdent => {
                let PathEndIdent { item, renamed_as: _ } = self.hir.path_end_ident(path);
                path_idents.push(item.ident.clone());
                path
            }
            NodeKind::PathEndStar | NodeKind::PathEndEmpty => {
                let parent = self.discover_data.parent_of(path);
                let PathSegment { prefix, suffix: _ } = self.hir.path_segment(parent);
                path_idents.push(prefix.last().unwrap().ident.clone());
                parent
            }
            _ => unreachable!(),
        };
        let (anchor, path_span, fn_args_key) = loop {
            path_node = self.discover_data.parent_of(path_node);
            let S { value, span } = self.hir.node_kind(path_node);
            match value {
                NodeKind::Path => {
                    let Path { anchor, segment: _ } = self.hir.path(path_node);

                    let parent = self.discover_data.parent_of(path_node);
                    let fn_args_key = if self.hir.node_kind(parent).value == NodeKind::FnCall {
                        Some(FnArgsKey::from_call(parent, self.hir))
                    } else {
                        None
                    };

                    break (anchor.map(|v| v.value), span, fn_args_key);
                }
                NodeKind::PathSegment => {
                    let PathSegment { prefix, suffix: _ } = self.hir.path_segment(path_node);
                    for PathItem { ident, ty_args: _ } in prefix.iter().rev() {
                        path_idents.push(ident.clone());
                    }
                }
                _ => unreachable!(),
            }
        };
        let fn_args_key = fn_args_key.as_ref();

        path_idents.reverse();

        let reso = if let Some(anchor) = anchor {
            Resolution::single(NsKind::Type, match anchor {
                PathAnchor::Package => (self.package_id, self.hir.root),
                PathAnchor::Root => unimplemented!(),
                PathAnchor::Super { count } => {
                    assert!(count > 0);
                    let mut scope = path;
                    for _ in 0..=count {
                        scope = if let Some(scope) = self.discover_data.try_module_of(scope) {
                            scope
                        } else {
                            fatal(path_span, "failed to resolve: too many leading `super` keywords");
                        };
                    }
                    (self.package_id, scope)
                }
            })
        } else {
            let scope = self.discover_data.scope_of(path);
            let first = path_idents.first().unwrap();
            let first = first.as_ref().map(|v| v.as_str());
            if let Some(reso) = self.resolve_in_scopes(scope, first, fn_args_key, paths).non_empty() {
                reso
            } else if let Some(package) = self.packages.try_by_name(&first.value) {
                Resolution::single(NsKind::Type, (package.id, package.hir.root))
            } else {
                let std_resolver = self.with_package(PackageId::std());
                // TODO cache this
                let std_prelude = std_resolver
                    .resolve_in_package(&["prelude", "v1"], None)
                    .node(NsKind::Type)
                    .unwrap();
                if_chain! {
                    if !paths.contains(&std_prelude);
                    if let Some(reso) = std_resolver.resolve_in_scope(std_prelude.1, first, fn_args_key, paths).non_empty();
                    then {
                        reso
                    } else {
                        if_chain! {
                            if path_idents.len() == 1;
                            if let Some(key) = fn_args_key;
                            then {
                                fatal(first.span, format_args!("could find function `{}::{}` in current scope", first.value, key));
                            } else {
                                fatal(first.span, format_args!("could find `{}` in current scope", first.value));
                            }
                        }
                    }
                }
            }
        };

        let more = path_idents.len() > if anchor.is_some() { 0 } else { 1 };
        let reso = if more {
            let (pkg, scope) = reso.type_or_other().unwrap();
            self.with_package(pkg)
                .resolve_path_idents(scope, anchor, &path_idents, fn_args_key, paths)
        } else {
            reso
        };

        assert!(!reso.is_empty());

        // TODO cache result.

        reso
    }

    fn resolve_path_idents(mut self,
        mut scope: NodeId,
        anchor: Option<PathAnchor>,
        path_idents: &[S<Ident>],
        fn_args_key: Option<&FnArgsKey>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Resolution {
        let mut r = Resolution::default();
        let start = if anchor.is_some() { 0 } else { 1 };
        for (i, ident) in path_idents.iter().enumerate().skip(start) {
            r = self.resolve_in_scope(
                scope,
                ident.as_ref().map(|v| v.as_str()),
                fn_args_key,
                paths,
            );
            if let Some((pkg, sc)) = r.type_or_other() {
                self = self.with_package(pkg);
                scope = sc;
            } else {
                let s = if i == 0 {
                    match anchor.unwrap() {
                        PathAnchor::Package => "package root",
                        PathAnchor::Root => "root",
                        PathAnchor::Super { .. } => "parent module",
                    }
                } else {
                    path_idents[i - 1].value.as_str()
                };
                if_chain! {
                    if i == path_idents.len() - 1;
                    if let Some(key) = fn_args_key;
                    then {
                        fatal(ident.span, format_args!("could find function `{}::{}` in `{}`", ident.value, key, s));
                    } else {
                        fatal(ident.span, format_args!("could not find `{}` in `{}`", ident.value, s));
                    }
                }
            }
        }
        assert!(!r.is_empty());
        r
    }

    fn resolve_in_scopes(&self,
        mut scope: NodeId,
        name: S<&str>,
        fn_args_key: Option<&FnArgsKey>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Resolution {
        loop {
            if let Some(r) = self.resolve_in_scope(scope, name, fn_args_key, paths).non_empty() {
                break r;
            }
            if self.hir.node_kind(scope).value == NodeKind::Module {
                break Resolution::default();
            }
            scope = if let Some(v) = self.discover_data.try_parent_scope_of(scope) {
                v
            } else {
                break Resolution::default();
            };
        }
    }

    fn resolve_in_scope(&self,
        scope: NodeId,
        name: S<&str>,
        fn_args_key: Option<&FnArgsKey>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Resolution {
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
                            r.set_node(ns_kind, (self.package_id, node));
                        }
                    },
                    Some(ScopeItem::Fns(fns)) => {
                        if let Some(key) = fn_args_key {
                            if let Some(fn_) = fns.iter().find(|f| &f.args_key == key) {
                                r.set_node(ns_kind, (self.package_id, fn_.node));
                            }
                        }
                    },
                    None => {}
                }

            } else {
                return r;
            }
        }
        if !r.is_empty() {
            return r;
        }
        let scope_ = self.discover_data.scope(scope, NsKind::Type);
        if !scope_.wildcard_imports().is_empty() {
            let mut found_in_wc_imports = Vec::new();
            for &path in scope_.wildcard_imports() {
                if paths.contains(&(self.package_id, path)) {
                    continue;
                }
                if let Some((pkg, scope)) = self.resolve(path, paths).type_or_other() {
                    let r = self.with_package(pkg)
                        .resolve_in_scope(scope, name, fn_args_key, paths);
                    if !r.is_empty() {
                        found_in_wc_imports.push(r);
                    }
                }
            }
            match found_in_wc_imports.len() {
                0 => {}
                1 => return found_in_wc_imports[0],
                _ => fatal(name.span,
                    format_args!("`{}` found in multiple wildcard imports", name.value)),
            }
        }
        Resolution::default()
    }
}