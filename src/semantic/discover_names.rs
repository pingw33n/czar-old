use enum_map::EnumMap;
use enum_map_derive::Enum;
use std::collections::hash_map::{Entry, HashMap};

use crate::syntax::*;
use crate::syntax::traverse::*;
use crate::util::EnumExt;

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

    pub fn scope_for(&self, kind: NsKind, node: NodeId) -> &Scope {
        &self.scopes[kind][&node]
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

pub struct MaintainNameScope<'a> {
    pub names: &'a mut Names,
}

impl AstVisitor for MaintainNameScope<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        let source_id = ctx.ast.try_module_decl(ctx.node).and_then(|m| m.source_id);
        self.names.push(ctx.node, source_id);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if ctx.kind != NodeKind::Let {
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
                let FnDeclArg { pub_name, priv_name, .. } = ctx.ast.fn_decl_arg(ctx.node);

                let _pub_name = pub_name.value.as_ref()
                    .map(|v| pub_name.span.spanned(v.clone()))
                    .unwrap_or_else(|| priv_name.clone());

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
            NodeKind::Let => {},
            NodeKind::LetDecl => {
                let name = ctx.ast.let_decl(ctx.node).name.clone();
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