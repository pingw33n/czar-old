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
                panic!("name `{}` is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
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
}

impl Names {
    pub fn resolve(&self, stack: &ScopeStack, kind: NsKind, name: &Ident) -> Option<NodeId> {
        let scopes = &self.scopes[kind];
        for scope_id in stack.iter() {
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

    pub fn scope(&self, kind: NsKind, node: NodeId) -> &Scope {
        self.try_scope(kind, node).unwrap()
    }

    pub fn try_scope(&self, kind: NsKind, node: NodeId) -> Option<&Scope> {
        self.scopes[kind].get(&node)
    }

    pub fn scope_mut(&mut self, kind: NsKind, node: NodeId) -> &mut Scope {
        self.scopes[kind].entry(node)
            .or_insert(Default::default())
    }

    pub fn print(&mut self, ast: &Ast) {
        struct Visitor<'a> {
            names: &'a Names,
            indent: u32,
        }

        impl AstVisitor for Visitor<'_> {
            fn before_node(&mut self, _ctx: AstVisitorCtx) {
                self.indent += 1;
            }

            fn node(&mut self, ctx: AstVisitorCtx) {
                for _ in 1..self.indent {
                    print!("  ");
                }
                let node = ctx.ast.node_kind(ctx.node);
                println!("{:?} {:?} {}:{}", node.value, ctx.node, node.span.start, node.span.end);
                for kind in NsKind::iter() {
                    if let Some(scope) = self.names.try_scope(kind, ctx.node) {
                        for _ in 1..self.indent {
                            print!("  ");
                        }
                        print!("| {:?}: ", kind);
                        for (i, (ident, &(span, node))) in scope.by_name.iter().enumerate() {
                            if i > 0 {
                                print!(", ");
                            }
                            let n = ctx.ast.node_kind(node);
                            print!("`{}` {}:{} -> {:?} {:?} {}:{}", ident, span.start, span.end,
                                n.value, node, n.span.start, n.span.end);
                        }
                        println!()
                    }
                }
            }

            fn after_node(&mut self, _ctx: AstVisitorCtx) {
                self.indent -= 1;
            }
        }

        AstTraverser {
            ast,
            visitor: &mut Visitor {
                names: self,
                indent: 0,
            },
        }.traverse();
    }
}

pub struct ScopeStack {
    stack: Vec<(NodeId, Option<SourceId>)>,
}

impl ScopeStack {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
        }
    }

    pub fn push(&mut self, node: NodeId, source_id: Option<SourceId>) {
        self.stack.push((node, source_id));
    }

    pub fn pop_until(&mut self, node: NodeId) {
        while self.stack.pop().unwrap().0 != node { }
    }

    pub fn top(&self) -> NodeId {
        self.stack.last().unwrap().0
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item=NodeId> + 'a {
        self.stack.iter().map(|&(n, _)| n).rev()
    }
}

pub struct AstScopeStack {
    stack: ScopeStack,
}

impl AstScopeStack {
    pub fn new() -> Self {
        Self {
            stack: ScopeStack::new(),
        }
    }

    fn is_scoped(kind: NodeKind) -> bool {
        use NodeKind::*;
        match kind {
            | Fn_
            | Let
            => false,

            | Block
            | BlockFlowCtl
            | Cast
            | FieldAccess
            | FnCall
            | FnDecl
            | FnDeclArg
            | IfExpr
            | Impl
            | LetDecl
            | Literal
            | Loop
            | ModuleDecl
            | Op
            | Range
            | StructDecl
            | StructType
            | StructValue
            | SymPath
            | TyExpr
            | TypeArg
            | UsePath
            | UseStmt
            | While
            => true,
        }
    }
}

impl AstVisitor for AstScopeStack {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        if Self::is_scoped(ctx.kind) {
            let source_id = ctx.ast.try_module_decl(ctx.node).and_then(|m| m.source_id);
            self.stack.push(ctx.node, source_id);
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if Self::is_scoped(ctx.kind) && ctx.kind != NodeKind::LetDecl {
            self.stack.pop_until(ctx.node);
        }
    }
}

impl std::ops::Deref for AstScopeStack {
    type Target = ScopeStack;

    fn deref(&self) -> &Self::Target {
        &self.stack
    }
}

pub struct DiscoverNames<'a> {
    stack: AstScopeStack,
    names: &'a mut Names,
}

impl<'a> DiscoverNames<'a> {
    pub fn new(names: &'a mut Names) -> Self {
        Self {
            stack: AstScopeStack::new(),
            names,
        }
    }
}

impl DiscoverNames<'_> {
    fn insert(&mut self, ns: NsKind, name: S<Ident>, node: NodeId) {
        self.names.scope_mut(ns, self.stack.top()).insert(name, node);
    }
}

impl AstVisitor for DiscoverNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        match ctx.kind {
            NodeKind::Fn_ => {}
            NodeKind::FnDecl => {
                let name = ctx.ast.fn_decl(ctx.node).name.clone();
                self.insert(NsKind::Value, name, ctx.node);
            },
            NodeKind::FnDeclArg => {
                let FnDeclArg { pub_name, priv_name, .. } = ctx.ast.fn_decl_arg(ctx.node);

                let _pub_name = pub_name.value.as_ref()
                    .map(|v| pub_name.span.spanned(v.clone()))
                    .unwrap_or_else(|| priv_name.clone());

                self.insert(NsKind::Value, priv_name.clone(), ctx.node);
            },
            NodeKind::ModuleDecl => {
                let name = &ctx.ast.module_decl(ctx.node).name;
                if let Some(name) = name {
                    self.insert(NsKind::Type, name.name.clone(), ctx.node);
                }
            }
            NodeKind::StructDecl => {
                let name = ctx.ast.struct_decl(ctx.node).name.clone();
                self.insert(NsKind::Type, name.clone(), ctx.node);
            }
            NodeKind::UsePath => {
                let UsePath { terms, .. } = ctx.ast.use_path(ctx.node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(PathTermIdent { ident, renamed_as }) => {
                            let name = renamed_as.as_ref()
                                .unwrap_or(ident);
                            for ns_kind in NsKind::iter() {
                                self.insert(ns_kind, name.clone(), ctx.node);
                            }
                        },
                        &PathTerm::Path(_) => {},
                        PathTerm::Star => {
                            for ns_kind in NsKind::iter() {
                                self.names.scope_mut(ns_kind, self.stack.top())
                                    .insert_wildcarded(ctx.node);
                            }
                        },
                    }
                }
            },
            NodeKind::Let => {},
            NodeKind::LetDecl => {
                let name = ctx.ast.let_decl(ctx.node).name.clone();
                self.insert(NsKind::Value, name, ctx.node);
            },
            | NodeKind::Block
            | NodeKind::BlockFlowCtl
            | NodeKind::Cast
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::IfExpr
            | NodeKind::Impl
            | NodeKind::Literal
            | NodeKind::Loop
            | NodeKind::Op
            | NodeKind::Range
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::SymPath
            | NodeKind::TyExpr
            | NodeKind::TypeArg
            | NodeKind::UseStmt
            | NodeKind::While
            => {},
        }
        self.stack.before_node(ctx);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.stack.after_node(ctx);
    }
}