use enum_map::EnumMap;
use enum_map_derive::Enum;
use slab::Slab;
use std::collections::hash_map::{Entry, HashMap};

use crate::syn::*;
use crate::syn::traverse::*;
use crate::util::EnumExt;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[repr(transparent)]
pub struct PackageId(pub usize);

impl PackageId {
    pub fn null() -> Self {
        Self(usize::max_value())
    }
}

pub struct Package {
    pub name: Ident,
    pub ast: Ast,
}

pub struct Context<'a> {
    pub packages: Slab<Package>,
    pub package_by_name: HashMap<Ident, PackageId>,
    pub ast: &'a Ast,
}



#[derive(Default)]
pub struct Scope {
    pub by_name: HashMap<Ident, (Span, NodeId)>,
    pub wildcarded: Vec<NodeId>,
}

impl Scope {
    pub fn insert(&mut self, name: S<Ident>, node: NodeId) {
        match self.by_name.entry(name.value) {
            Entry::Occupied(e) => {
                let first = e.get().0;
                let this = name.span;
                eprintln!("name `{}` is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
                    e.key(), first.start, first.end, this.start, this.end);
            },
            Entry::Vacant(e) => {
                e.insert((name.span, node));
            },
        }
    }

    pub fn insert_wildcarded(&mut self, node: NodeId) {
        self.wildcarded.push(node);
    }
}

#[derive(Clone, Copy, Debug, Enum)]
pub enum NsKind {
    Misc,
    Type,
    Value,
}

#[derive(Default)]
pub struct Names {
    scopes: EnumMap<NsKind, NodeMap<Scope>>,
    stack: Vec<(NodeId, Option<SourceId>)>,
}

impl Names {
    pub fn push(&mut self, node: NodeId, source_id: Option<SourceId>) {
        self.stack.push((node, source_id));
    }

    pub fn pop_until(&mut self, node: NodeId) {
        while self.stack.pop().unwrap().0 != node { }
    }

    pub fn resolve(&self, kind: NsKind, name: &Ident) -> Option<NodeId> {
        let scopes = &self.scopes[kind];
        for &(scope_id, _) in self.stack.iter().rev() {
            if let Some(r) = scopes.get(&scope_id)
                .and_then(|s| {
                    let r = s.by_name.get(name).map(|&(_, n)| n);
                    if !s.wildcarded.is_empty() {
                        unimplemented!();
                    }
                    r
                })
            {
                return Some(r);
            }
        }
        None
    }

    pub fn scope_mut(&mut self, kind: NsKind) -> &mut Scope {
        let cur = self.cur_scope();
        self.scopes[kind].entry(cur)
            .or_insert(Default::default())
    }

    pub fn print(&self, ast: &Ast) {
        for kind in NsKind::iter() {
            println!("{:?}", kind);
            let scopes = &self.scopes[kind];
            for (&n, s) in scopes {
                println!("  {:?}", ast.node_kind(n));
                for (ident, &(span, node)) in &s.by_name {
                    println!("    {:?} -> {:?}", span.spanned(ident), ast.node_kind(node));
                }
            }
        }
    }

    fn cur_scope(&self) -> NodeId {
        self.stack.last().unwrap().0
    }
}

struct MaintainNameScope<'a> {
    pub names: &'a mut Names,
}

impl AstVisitor for MaintainNameScope<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        let source_id = ctx.ast.try_module_decl(ctx.node).and_then(|m| m.source_id);
        self.names.push(ctx.node, source_id);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if ctx.kind != NodeKind::VarDecl {
            self.names.pop_until(ctx.node);
        }
    }
}

pub struct DiscoverNames<'a> {
    names: MaintainNameScope<'a>,
}

impl<'a> DiscoverNames<'a> {
    pub fn new(names: &'a mut Names) -> Self {
        Self {
            names: MaintainNameScope { names },
        }
    }
}

impl AstVisitor for DiscoverNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        match ctx.kind {
            NodeKind::FnDecl => {
                let name = ctx.ast.fn_decl(ctx.node).name.clone();
                self.names.names.scope_mut(NsKind::Value).insert(name, ctx.node);
            },
            NodeKind::FnDeclArg => {
                let FnDeclArg { pub_name, priv_name, ty: _ } = ctx.ast.fn_decl_arg(ctx.node);

                let pub_name = pub_name.value.as_ref()
                    .map(|v| pub_name.span.spanned(v.clone()))
                    .unwrap_or_else(|| priv_name.clone());
                self.names.names.scope_mut(NsKind::Misc).insert(pub_name, ctx.node);

                self.names.names.scope_mut(NsKind::Value).insert(priv_name.clone(), ctx.node);
            },
            NodeKind::ModuleDecl => {
                let name = &ctx.ast.module_decl(ctx.node).name;
                if let Some(name) = name {
                    self.names.names.scope_mut(NsKind::Type).insert(name.name.clone(), ctx.node);
                }
            }
            NodeKind::StructDecl => {
                let name = ctx.ast.struct_decl(ctx.node).name.clone();
                self.names.names.scope_mut(NsKind::Type).insert(name.clone(), ctx.node);
            }
            NodeKind::UsePath => {
                let UsePath { terms, .. } = ctx.ast.use_path(ctx.node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(PathTermIdent { ident, renamed_as }) => {
                            let name = renamed_as.as_ref()
                                .unwrap_or(ident);
                            for &ns_kind in &[NsKind::Type, NsKind::Value] {
                                self.names.names.scope_mut(ns_kind).insert(name.clone(), ctx.node);
                            }
                        },
                        &PathTerm::Path(_) => {},
                        PathTerm::Star => {
                            for &ns_kind in &[NsKind::Type, NsKind::Value] {
                                self.names.names.scope_mut(ns_kind).insert_wildcarded(ctx.node);
                            }
                        },
                    }
                }
            },
            NodeKind::VarDecl => {
                let name = ctx.ast.var_decl(ctx.node).name.clone();
                self.names.names.scope_mut(NsKind::Value).insert(name, ctx.node);
            },
            NodeKind::Block => {}
            NodeKind::BlockFlowCtl => {},
            NodeKind::Cast => {},
            NodeKind::FieldAccess => {},
            NodeKind::FnCall => {},
            NodeKind::IfExpr => {}
            NodeKind::Impl => {}
            NodeKind::Literal => {}
            NodeKind::Loop => {}
            NodeKind::Op => {}
            NodeKind::Range => {}
            NodeKind::StructType => {}
            NodeKind::StructValue => {}
            NodeKind::SymPath => {}
            NodeKind::TyExpr => {}
            NodeKind::TypeArg => {}
            NodeKind::UseStmt => {}
            NodeKind::While => {}
        }
        self.names.before_node(ctx);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.names.after_node(ctx);
    }
}

#[derive(Default)]
pub struct ResolvedNames {
    namespaces: EnumMap<NsKind, NodeMap<NodeId>>,
}

impl ResolvedNames {
    pub fn insert(&mut self, ns_kind: NsKind, node: NodeId, resolved: NodeId) {
        assert!(self.namespaces[ns_kind].insert(node, resolved).is_none());
    }
}

pub struct ResolveNames<'a> {
    names: MaintainNameScope<'a>,
    resolved_names: &'a mut ResolvedNames,
    ns_kind_stack: Vec<NsKind>,
}

impl<'a> ResolveNames<'a> {
    pub fn new(names: &'a mut Names, resolved_names: &'a mut ResolvedNames) -> Self {
        Self {
            names: MaintainNameScope { names },
            resolved_names,
            ns_kind_stack: Vec::new(),
        }
    }

    fn push_ns_kind(&mut self, link_kind: NodeLinkKind) {
        use NodeLinkKind::*;
        let ns_kind = match link_kind {
            | BlockExpr
            | BlockFlowCtlValue
            | Cast(CastLink::Expr)
            | FieldAccessReceiver
            | FnCall(_)
            | FnDecl(FnDeclLink::Body)
            | IfExpr(_)
            | LoopBlock
            | Op(_)
            | Range(_)
            | StructValueValue
            | TyExpr(TyExprLink::Array(ArrayLink::Len))
            | VarDecl(VarDeclLink::Init)
            | While(_)
            => NsKind::Value,

            | Cast(CastLink::Type)
            | FnDecl(_)
            | FnDeclArgType
            | Impl(_)
            | ModuleItem
            | Root
            | StructDecl(_)
            | StructTypeFieldType
            | SymPathTypeArg
            | TyExpr(_)
            | UsePathPath
            | UseStmtPath
            | VarDecl(VarDeclLink::Type)
            => NsKind::Type,
        };
        self.ns_kind_stack.push(ns_kind);
    }
}

impl AstVisitor for ResolveNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        self.names.before_node(ctx);
    }

    fn node(&mut self, ctx: AstVisitorCtx) {
        self.push_ns_kind(ctx.link_kind);

        match ctx.kind {
            NodeKind::SymPath => {
                let SymPath { anchor, items } = ctx.ast.sym_path(ctx.node);
                if anchor.is_some() {
                    unimplemented!();
                }
                let first = &items[0].ident;
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                if let Some(resolved) = self.names.names.resolve(ns_kind, &first.value) {
                    if items.len() > 1 {
                        unimplemented!();
                    }
                    self.resolved_names.insert(ns_kind, ctx.node, resolved);
                } else {
                    eprintln!("[{}:{}] couldn't find name `{}` in the current scope",
                        first.span.start, first.span.end, first.value);
                }
            }
            _ => {}
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.names.after_node(ctx);
        self.ns_kind_stack.pop().unwrap();
    }
}