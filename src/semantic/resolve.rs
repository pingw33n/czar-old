use enum_as_inner::EnumAsInner;
use std::collections::HashSet;

use crate::syntax::*;
use crate::syntax::traverse::*;

use super::*;
use super::discover::{DiscoverData, NsKind};


#[derive(Debug, Default)]
pub struct ResolveData {
    path_to_target: NodeMap<NodeId>,
}

impl ResolveData {
    pub fn build(discover: &DiscoverData, ast: &Ast) -> Self {
        let mut resolve = ResolveData::default();
        AstTraverser {
            ast: &ast,
            visitor: &mut Build {
                discover,
                resolve: &mut resolve,
                ns_kind_stack: Vec::new(),
            },
        }.traverse();
        resolve
    }

    pub fn insert(&mut self, node: NodeId, target: NodeId) {
        assert!(self.path_to_target.insert(node, target).is_none());
    }

    pub fn target_of(&self, path: NodeId) -> NodeId {
        self.path_to_target[&path]
    }

    pub fn try_target_of(&self, path: NodeId) -> Option<NodeId> {
        self.path_to_target.get(&path).copied()
    }
}

struct Build<'a> {
    discover: &'a DiscoverData,
    resolve: &'a mut ResolveData,
    ns_kind_stack: Vec<NsKindOption>,
}

impl<'a> Build<'a> {
    fn ns_kind(link_kind: NodeLinkKind) -> Option<NsKindOption> {
        use NodeLinkKind::*;
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

    fn push_ns_kind(&mut self, link_kind: NodeLinkKind) {
        if let Some(v) = Self::ns_kind(link_kind) {
            self.ns_kind_stack.push(v);
        }
    }
}

impl AstVisitor for Build<'_> {
    fn node(&mut self, ctx: AstVisitorCtx) {
        self.push_ns_kind(ctx.link_kind);

        match ctx.kind {
            NodeKind::PathEndIdent | NodeKind::PathEndStar => {
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                Resolver {
                    discover: self.discover,
                    resolve: self.resolve,
                    ast: ctx.ast,
                }.resolve(ns_kind, ctx.node);
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if let Some(v) = Self::ns_kind(ctx.link_kind) {
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

pub struct Resolver<'a> {
    pub discover: &'a DiscoverData,
    pub resolve: &'a mut ResolveData,
    pub ast: &'a Ast,
}

impl<'a> Resolver<'a> {
    pub fn resolve(&mut self, ns_kind: NsKindOption, path: NodeId) -> NodeId {
        self.resolve0(ns_kind, &mut HashSet::new(), path)
    }

    fn resolve0(&mut self,
        ns_kind: NsKindOption,
        paths: &mut HashSet<NodeId>,
        path: NodeId,
    ) -> NodeId {
        if let Some(resolved) = self.resolve.try_target_of(path) {
            return resolved;
        }

        assert!(paths.insert(path));

        let mut path_idents = Vec::new();
        let (mut path_node, ns_kind) = match self.ast.node_kind(path).value {
            NodeKind::PathEndIdent => {
                let PathEndIdent { item, renamed_as: _ } = self.ast.path_end_ident(path);
                path_idents.push(item.ident.clone());
                (path, ns_kind)
            }
            NodeKind::PathEndStar | NodeKind::PathEndEmpty => {
                let parent = self.discover.parent_of(path);
                let PathSegment { prefix, suffix: _ } = self.ast.path_segment(parent);
                path_idents.push(prefix.last().unwrap().ident.clone());
                (parent, NsKindOption::Require(NsKind::Type))
            }
            _ => unreachable!(),
        };
        let (anchor, path_span) = loop {
            path_node = self.discover.parent_of(path_node);
            let S { value, span } = self.ast.node_kind(path_node);
            match value {
                NodeKind::Path => {
                    let Path { anchor, segment: _ } = self.ast.path(path_node);
                    break (anchor.map(|v| v.value), span);
                }
                NodeKind::PathSegment => {
                    let PathSegment { prefix, suffix: _ } = self.ast.path_segment(path_node);
                    for PathItem { ident, ty_args: _ } in prefix.iter().rev() {
                        path_idents.push(ident.clone());
                    }
                }
                _ => unreachable!(),
            }
        };

        path_idents.reverse();

        let import = self.ast.node_kind(self.discover.parent_of(path_node)).value == NodeKind::UseStmt;

        let mut node = if let Some(anchor) = anchor {
            match anchor {
                PathAnchor::Package => self.ast.root,
                PathAnchor::Root => unimplemented!(),
                PathAnchor::Super { count } => {
                    assert!(count > 0);
                    let mut scope = path;
                    for _ in 0..=count {
                        scope = if let Some(scope) = self.discover.try_module_of(scope) {
                            scope
                        } else {
                            fatal(path_span, "failed to resolve: too many leading `super` keywords");
                        };
                    }
                    scope
                }
            }
        } else {
            let scope = self.discover.scope_of(path);
            let first = path_idents.first().unwrap();
            let first = first.as_ref().map(|v| v.as_str());
            let first_ns_kind = if path_idents.len() == 1 {
                ns_kind
            } else {
                NsKindOption::Require(NsKind::Type)
            };
            if let Some(node) = self.resolve_in_scopes(scope, first_ns_kind, first, paths) {
                node
            } else {
                fatal(first.span, format_args!("could find `{}` in current scope", first.value));
            }
        };

        let start = if anchor.is_some() {
            0
        } else {
            1
        };
        for (i, ident) in path_idents.iter().enumerate().skip(start) {
            let this_ns_kind = if i < path_idents.len() - 1 {
                ns_kind
            } else {
                NsKindOption::Require(NsKind::Type)
            };
            if let Some(n) = self.resolve_in_scope(
                node,
                this_ns_kind,
                ident.as_ref().map(|v| v.as_str()),
                paths,
            ) {
                node = n;
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
        if !import {
            self.resolve.insert(path, node);
        } else {
            // TODO cache import resolution.
            if self.ast.node_kind(node).value == NodeKind::LetDecl {
                fatal(path_span, "can't import variable definition");
            }
        }
        node
    }

    fn resolve_in_scopes(&mut self,
        mut scope: NodeId,
        ns_kind: NsKindOption,
        name: S<&str>,
        paths: &mut HashSet<NodeId>,
    ) -> Option<NodeId> {
        loop {
            let r = self.resolve_in_scope(scope, ns_kind, name, paths);
            if r.is_some() {
                return r;
            }
            scope = self.discover.try_parent_scope_of(scope)?;
        }
    }

    fn resolve_in_scope(&mut self,
        scope: NodeId,
        ns_kind_option: NsKindOption,
        name: S<&str>,
        paths: &mut HashSet<NodeId>,
    ) -> Option<NodeId> {
        for ns_kind in ns_kind_option.iter() {
            let scope_ = self.discover.try_scope(scope, ns_kind)?;
            let node = scope_.try_get(name.value).map(|v| v.node);
            if let Some(node) = node {
                if !paths.contains(&node) {
                    return Some(if self.ast.node_kind(node).value == NodeKind::PathEndIdent {
                        self.resolve0(ns_kind_option, paths, node)
                    } else {
                        node
                    })
                }
            }
            if !scope_.wildcard_imports().is_empty() {
                let mut found_in_wc_imports = Vec::new();
                for &path in scope_.wildcard_imports() {
                    if paths.contains(&path) {
                        continue;
                    }
                    let scope = self.resolve0(NsKindOption::Require(NsKind::Type), paths, path);
                    if let Some(n) = self.resolve_in_scope(scope, ns_kind_option, name, paths) {
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
