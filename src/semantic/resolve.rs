use enum_as_inner::EnumAsInner;
use std::collections::HashSet;

use crate::hir::*;
use crate::hir::traverse::*;
use crate::package::{GlobalNodeId, PackageId, Packages};

use super::*;
use super::discover::{DiscoverData, NsKind};

#[derive(Debug, Default)]
pub struct ResolveData {
    path_to_target: NodeMap<GlobalNodeId>,
}

impl ResolveData {
    pub fn build(discover_data: &DiscoverData, hir: &Hir, package_id: PackageId, packages: &Packages) -> Self {
        let mut resolve_data = ResolveData::default();
        hir.traverse(&mut Build {
            discover_data,
            resolve_data: &mut resolve_data,
            package_id,
            packages,
            ns_kind_stack: Vec::new(),
        });
        resolve_data
    }

    pub fn insert(&mut self, node: NodeId, target: GlobalNodeId) {
        assert!(self.path_to_target.insert(node, target).is_none());
    }

    pub fn target_of(&self, path: NodeId) -> GlobalNodeId {
        self.path_to_target[&path]
    }

    pub fn try_target_of(&self, path: NodeId) -> Option<GlobalNodeId> {
        self.path_to_target.get(&path).copied()
    }
}

struct Build<'a> {
    discover_data: &'a DiscoverData,
    resolve_data: &'a mut ResolveData,
    package_id: PackageId,
    packages: &'a Packages,
    ns_kind_stack: Vec<NsKindOption>,
}

impl<'a> Build<'a> {
    fn ns_kind(link_kind: NodeLink) -> Option<NsKindOption> {
        use NodeLink::*;
        Some(match link_kind {
            | BlockExpr
            | BlockFlowCtlValue
            | Cast(CastLink::Expr)
            | FieldAccessReceiver
            | FnCall(_)
            | Fn(FnLink::Body)
            | IfExpr(_)
            | Let(LetLink::Init)
            | LoopBlock
            | Op(_)
            | Range(_)
            | StructValueValue
            | TyExpr(TyExprLink::Array(ArrayLink::Len))
            | While(_)
            => NsKindOption::Prefer(NsKind::Value),

            | Cast(CastLink::Type)
            | Fn(FnLink::TypeArg)
            | Fn(FnLink::RetType)
            | FnDeclArgType
            | Impl(ImplLink::TypeArg)
            | Let(LetLink::Type)
            | Path(PathLink::EndIdentTyArgs)
            | Path(PathLink::SegmentItemTyArgs)
            | StructDecl(_)
            | StructTypeFieldType
            | TyExpr(_)
            => NsKindOption::Prefer(NsKind::Type),

            UseStmtPath => NsKindOption::Any,

            | Fn(_)
            | Impl(_)
            | Let(_)
            | ModuleItem
            | Path(_)
            | Root
            => return None,
        })
    }

    fn push_ns_kind(&mut self, link_kind: NodeLink) {
        if let Some(v) = Self::ns_kind(link_kind) {
            self.ns_kind_stack.push(v);
        }
    }
}

impl HirVisitor for Build<'_> {
    fn node(&mut self, ctx: HirVisitorCtx) {
        self.push_ns_kind(ctx.link);

        match ctx.kind {
            NodeKind::PathEndIdent | NodeKind::PathEndStar => {
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                let target = Resolver {
                    discover_data: self.discover_data,
                    resolve_data: self.resolve_data,
                    hir: ctx.hir,
                    package_id: self.package_id,
                    packages: self.packages,
                }.resolve_node(ns_kind, ctx.node);
                self.resolve_data.insert(ctx.node, target);
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        if let Some(v) = Self::ns_kind(ctx.link) {
            assert_eq!(self.ns_kind_stack.pop().unwrap(), v);
        }
    }
}

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, PartialEq)]
pub enum NsKindOption {
    Prefer(NsKind),
    Require(NsKind),
    Any,
}

impl NsKindOption {
    pub fn iter(self) -> impl Iterator<Item=NsKind> + 'static {
        let (first, second) = match self {
            Self::Prefer(v) => (v, Some(v.other())),
            Self::Require(v) => (v, None),
            Self::Any => (NsKind::Type, Some(NsKind::Value)),
        };

        #[derive(Clone, Copy)]
        enum State {
            First {
                first: NsKind,
                second: Option<NsKind>,
            },
            Second(NsKind),
            End,
        }
        struct Iter(State);
        impl Iterator for Iter {
            type Item = NsKind;

            fn next(&mut self) -> Option<Self::Item> {
                Some(match self.0 {
                    State::First { first, second } => {
                        self.0 = if let Some(second) = second {
                            State::Second(second)
                        } else {
                            State::End
                        };
                        first
                    }
                    State::Second(second) => {
                        self.0 = State::End;
                        second
                    }
                    State::End => return None,
                })
            }
        }
        Iter(State::First { first, second })
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
    pub fn resolve_node(&self, ns_kind: NsKindOption, path: NodeId) -> GlobalNodeId {
        self.resolve0(ns_kind, &mut HashSet::new(), path)
    }

    pub fn resolve_in_package(&self,
        ns_kind: NsKindOption,
        path: &[&str],
    ) -> GlobalNodeId {
        let path_idents: Vec<_> = path
            .iter()
            .map(|&s| Span::new(0, 0).spanned(Ident::from(s)))
            .collect();
        self.clone().resolve_path_idents(
            self.hir.root,
            ns_kind,
            Some(PathAnchor::Package),
            &path_idents,
            &mut HashSet::new(),
        )
    }

    fn with_package(&self, package_id: PackageId) -> Self {
        if package_id == self.package_id {
            self.clone()
        } else {
            let package = self.packages.get(package_id);
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
            &self.packages.get(package_id).hir
        }
    }

    fn resolve0(&self,
        ns_kind: NsKindOption,
        paths: &mut HashSet<GlobalNodeId>,
        path: NodeId,
    ) -> GlobalNodeId {
        if let Some(resolved) = self.resolve_data.try_target_of(path) {
            return resolved;
        }

        assert!(paths.insert((self.package_id, path)));

        let mut path_idents = Vec::new();
        let (mut path_node, ns_kind) = match self.hir.node_kind(path).value {
            NodeKind::PathEndIdent => {
                let PathEndIdent { item, renamed_as: _ } = self.hir.path_end_ident(path);
                path_idents.push(item.ident.clone());
                (path, ns_kind)
            }
            NodeKind::PathEndStar | NodeKind::PathEndEmpty => {
                let parent = self.discover_data.parent_of(path);
                let PathSegment { prefix, suffix: _ } = self.hir.path_segment(parent);
                path_idents.push(prefix.last().unwrap().ident.clone());
                (parent, NsKindOption::Require(NsKind::Type))
            }
            _ => unreachable!(),
        };
        let (anchor, path_span) = loop {
            path_node = self.discover_data.parent_of(path_node);
            let S { value, span } = self.hir.node_kind(path_node);
            match value {
                NodeKind::Path => {
                    let Path { anchor, segment: _ } = self.hir.path(path_node);
                    break (anchor.map(|v| v.value), span);
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

        path_idents.reverse();

        let import = self.hir.node_kind(self.discover_data.parent_of(path_node)).value == NodeKind::UseStmt;

        let (pkg, node) = if let Some(anchor) = anchor {
            match anchor {
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
            }
        } else {
            let scope = self.discover_data.scope_of(path);
            let first = path_idents.first().unwrap();
            let first = first.as_ref().map(|v| v.as_str());
            let first_ns_kind = if path_idents.len() == 1 {
                ns_kind
            } else {
                NsKindOption::Require(NsKind::Type)
            };
            if let Some(node) = self.resolve_in_scopes(scope, first_ns_kind, first, paths) {
                node
            } else if let Some(package_id) = self.packages.try_by_name(&first.value) {
                let package = self.packages.get(package_id);
                (package_id, package.hir.root)
            } else {
                fatal(first.span, format_args!("could find `{}` in current scope", first.value));
            }
        };

        let node = self.with_package(pkg)
            .resolve_path_idents(node, ns_kind, anchor, &path_idents, paths);

        if import && self.hir(node.0).node_kind(node.1).value == NodeKind::LetDecl {
            fatal(path_span, "can't import variable definition");
        }

        // TODO cache results.

        node
    }

    fn resolve_path_idents(mut self,
        mut scope: NodeId,
        ns_kind: NsKindOption,
        anchor: Option<PathAnchor>,
        path_idents: &[S<Ident>],
        paths: &mut HashSet<GlobalNodeId>,
    ) -> GlobalNodeId {
        let start = if anchor.is_some() { 0 } else { 1 };
        for (i, ident) in path_idents.iter().enumerate().skip(start) {
            let this_ns_kind = if i < path_idents.len() - 1 {
                ns_kind
            } else {
                NsKindOption::Require(NsKind::Type)
            };
            if let Some((package, node)) = self.resolve_in_scope(
                scope,
                this_ns_kind,
                ident.as_ref().map(|v| v.as_str()),
                paths,
            ) {
                scope = node;
                self = self.with_package(package)
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
                fatal(ident.span, format_args!("could not find `{}` in `{}`", ident.value, s));
            }
        }
        (self.package_id, scope)
    }

    fn resolve_in_scopes(&self,
        mut scope: NodeId,
        ns_kind: NsKindOption,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Option<GlobalNodeId> {
        loop {
            let r = self.resolve_in_scope(scope, ns_kind, name, paths);
            if r.is_some() {
                return r;
            }
            if self.hir.node_kind(scope).value == NodeKind::Module {
                let std_resolver = self.with_package(PackageId::std());
                let std_prelude = std_resolver
                    .resolve_in_package(NsKindOption::Require(NsKind::Type), &["prelude", "v1"]);
                break std_resolver.resolve_in_scope(std_prelude.1, ns_kind, name, paths);
            }
            scope = self.discover_data.try_parent_scope_of(scope)?;
        }
    }

    fn resolve_in_scope(&self,
        scope: NodeId,
        ns_kind_option: NsKindOption,
        name: S<&str>,
        paths: &mut HashSet<GlobalNodeId>,
    ) -> Option<GlobalNodeId> {
        for ns_kind in ns_kind_option.iter() {
            let scope_ = self.discover_data.try_scope(scope, ns_kind)?;
            let node = scope_.try_get(name.value).map(|v| v.node);
            if let Some(node) = node {
                if !paths.contains(&(self.package_id, node)) {
                    return Some(if self.hir.node_kind(node).value == NodeKind::PathEndIdent {
                        self.resolve0(ns_kind_option, paths, node)
                    } else {
                        (self.package_id, node)
                    })
                }
            }
            if !scope_.wildcard_imports().is_empty() {
                let mut found_in_wc_imports = Vec::new();
                for &path in scope_.wildcard_imports() {
                    if paths.contains(&(self.package_id, path)) {
                        continue;
                    }
                    let (pkg, scope) = self.resolve0(NsKindOption::Require(NsKind::Type), paths, path);
                    if let Some(n) = self.with_package(pkg)
                        .resolve_in_scope(scope, ns_kind_option, name, paths)
                    {
                        found_in_wc_imports.push(n);
                    }
                }
                match found_in_wc_imports.len() {
                    0 => {}
                    1 => return Some(found_in_wc_imports[0]),
                    _ => fatal(name.span,
                        format_args!("`{}` found in multiple wildcard imports", name.value)),
                }
            }
        }
        None
    }
}
