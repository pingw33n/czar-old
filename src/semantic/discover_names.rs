use enum_map::EnumMap;
use enum_map_derive::Enum;
use std::collections::hash_map::{Entry, HashMap};

use crate::syntax::*;
use crate::syntax::traverse::*;
use crate::util::EnumExt;

pub struct Item {
    pub name: S<Ident>,
    pub node: NodeId,
}

#[derive(Default)]
pub struct Scope {
    pub by_name: HashMap<Ident, Item>,
    pub wildcarded: Vec<NodeId>,
}

impl Scope {
    pub fn insert(&mut self, name: S<Ident>, node: NodeId) {
        match self.by_name.entry(name.value.clone()) {
            Entry::Occupied(e) => {
                let first = e.get().name.span;
                let this = name.span;
                panic!("name `{}` is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
                    e.key(), first.start, first.end, this.start, this.end);
            },
            Entry::Vacant(e) => {
                e.insert(Item {
                    name,
                    node,
                });
            },
        }
    }

    pub fn insert_wildcarded(&mut self, node: NodeId) {
        self.wildcarded.push(node);
    }

    pub fn is_empty(&self) -> bool {
        self.by_name.is_empty() && self.wildcarded.is_empty()
    }
}

#[derive(Clone, Copy, Debug, Enum, Eq, PartialEq)]
pub enum NsKind {
    Type,
    Value,
}

#[derive(Default)]
pub struct Names {
    scopes: NodeMap<EnumMap<NsKind, Scope>>,
}

impl Names {
    pub fn resolve(&self, stack: &ScopeStack, kind: NsKind, name: &Ident) -> Option<NodeId> {
        for scope_id in stack.iter() {
            if let Some(r) = self.scopes.get(&scope_id)
                .and_then(|s| {
                    let s = &s[kind];
                    let r = s.by_name.get(name).map(|&Item { node, .. }| node);
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
        self.scopes.get(&node).map(|s| &s[kind])
    }

    pub fn scope_mut(&mut self, kind: NsKind, node: NodeId) -> &mut Scope {
        &mut self.scopes.entry(node)
            .or_insert(Default::default())
            [kind]
    }

    pub fn print(&mut self, ast: &Ast) {
        struct Visitor<'a> {
            names: &'a Names,
            indent: u32,
        }

        impl Visitor<'_> {
            fn print_indent(&self) {
                for _ in 1..self.indent {
                    print!("  ");
                }
            }
        }

        impl AstVisitor for Visitor<'_> {
            fn before_node(&mut self, _ctx: AstVisitorCtx) {
                self.indent += 1;
            }

            fn node(&mut self, ctx: AstVisitorCtx) {
                self.print_indent();
                let node = ctx.ast.node_kind(ctx.node);
                if let Some(name) = ctx.ast.try_module_decl(ctx.node)
                    .and_then(|ModuleDecl { name, .. }| name.as_ref())
                {
                    println!("{:?} {:?} `{}` {}:{}",
                        node.value, ctx.node, name.name.value, node.span.start, node.span.end);
                } else {
                    println!("{:?} {:?} {}:{}",
                        node.value, ctx.node, node.span.start, node.span.end);
                }
                for kind in NsKind::iter() {
                    if let Some(scope) = self.names.try_scope(kind, ctx.node) {
                        if !scope.is_empty() {
                            self.print_indent();
                            print!("| {:?}: ", kind);
                            for (i, (ident, Item { node, name })) in
                                scope.by_name.iter().enumerate()
                            {
                                if i > 0 {
                                    print!(", ");
                                }
                                let n = ctx.ast.node_kind(*node);
                                print!("`{}` {}:{} -> {:?} {:?} {}:{}", ident,
                                    name.span.start, name.span.end,
                                    n.value, node, n.span.start, n.span.end);
                            }
                            println!()
                        }
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
    stack: Vec<NodeId>,
}

impl ScopeStack {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
        }
    }

    pub fn push(&mut self, node: NodeId) {
        self.stack.push(node);
    }

    pub fn pop_until(&mut self, node: NodeId) {
        while self.stack.pop().unwrap() != node { }
    }

    pub fn top(&self) -> NodeId {
        *self.stack.last().unwrap()
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item=NodeId> + 'a {
        self.stack.iter().copied().rev()
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
            | Path
            | PathEndEmpty
            | PathEndIdent
            | PathEndStar
            | PathSegment
            | UseStmt
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
            | TyExpr
            | TypeArg
            | While
            => true,
        }
    }
}

impl AstVisitor for AstScopeStack {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        if Self::is_scoped(ctx.kind) {
            self.stack.push(ctx.node);
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

struct DiscoverNames<'a> {
    stack: AstScopeStack,
    names: &'a mut Names,

    /// Is in `Use` subtree?
    in_use: bool,
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
                let ModuleDecl { name, .. } = &ctx.ast.module_decl(ctx.node);
                if let Some(name) = name {
                    self.insert(NsKind::Type, name.name.clone(), ctx.node);
                }
            }
            NodeKind::StructDecl => {
                let name = ctx.ast.struct_decl(ctx.node).name.clone();
                self.insert(NsKind::Type, name.clone(), ctx.node);
            }
            NodeKind::PathEndIdent if self.in_use => {
                let PathEndIdent {
                    item: PathItem { ident, ty_args: _, .. },
                    renamed_as,
                } = ctx.ast.path_end_ident(ctx.node);
                let name = renamed_as.as_ref().unwrap_or(ident);
                for ns_kind in NsKind::iter() {
                    self.insert(ns_kind, name.clone(), ctx.node);
                }
            },
            NodeKind::PathEndStar => {
                assert!(self.in_use);
                for ns_kind in NsKind::iter() {
                    self.names.scope_mut(ns_kind, self.stack.top())
                        .insert_wildcarded(ctx.node);
                }
            }
            NodeKind::Let => {},
            NodeKind::LetDecl => {
                let name = ctx.ast.let_decl(ctx.node).name.clone();
                self.insert(NsKind::Value, name, ctx.node);
            },
            NodeKind::UseStmt => {
                assert!(!self.in_use);
                self.in_use = false;
            }
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
            | NodeKind::Path
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndIdent
            | NodeKind::PathSegment
            | NodeKind::Range
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::TyExpr
            | NodeKind::TypeArg
            | NodeKind::While
            => {},
        }
        self.stack.before_node(ctx);
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        self.stack.after_node(ctx);
        if ctx.kind == NodeKind::UseStmt {
            assert!(self.in_use);
            self.in_use = false;
        }
    }
}

pub fn discover_names(names: &mut Names, ast: &Ast) {
    AstTraverser {
        ast,
        visitor: &mut DiscoverNames {
            stack: AstScopeStack::new(),
            names,
            in_use: false,
        },
    }.traverse();
}