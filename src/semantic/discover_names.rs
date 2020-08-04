use enum_map::EnumMap;
use enum_map_derive::Enum;
use std::collections::hash_map::{Entry, HashMap};

use crate::syntax::*;
use crate::syntax::traverse::*;
use crate::util::enums::EnumExt;

pub struct ScopeItem {
    pub name: S<Ident>,
    pub node: NodeId,
}

#[derive(Default)]
pub struct Scope {
    items: HashMap<Ident, ScopeItem>,
    wildcard_imports: Vec<NodeId>,
}

impl Scope {
    pub fn insert(&mut self, name: S<Ident>, node: NodeId) {
        match self.items.entry(name.value.clone()) {
            Entry::Occupied(e) => {
                let first = e.get().name.span;
                let this = name.span;
                panic!("name `{}` is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
                    e.key(), first.start, first.end, this.start, this.end);
            },
            Entry::Vacant(e) => {
                e.insert(ScopeItem {
                    name,
                    node,
                });
            },
        }
    }

    pub fn try_get(&self, name: &str) -> Option<&ScopeItem> {
        self.items.get(name)
    }

    pub fn get(&self, name: &str) -> &ScopeItem {
        self.try_get(name).unwrap()
    }

    pub fn insert_wildcard_import(&mut self, node: NodeId) {
        self.wildcard_imports.push(node);
    }

    pub fn wildcard_imports(&self) -> &[NodeId] {
        &self.wildcard_imports
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty() && self.wildcard_imports.is_empty()
    }
}

#[derive(Clone, Copy, Debug, Enum, Eq, PartialEq)]
pub enum NsKind {
    Type,
    Value,
}

impl NsKind {
    pub fn other(self) -> Self {
        match self {
            Self::Type => Self::Value,
            Self::Value => Self::Type,
        }
    }
}

#[derive(Default)]
pub struct Names {
    scopes: NodeMap<EnumMap<NsKind, Scope>>,
    scope_to_parent: NodeMap<NodeId>,
    node_to_scope: NodeMap<NodeId>,
    child_to_parent: NodeMap<NodeId>,
    node_to_module: NodeMap<NodeId>,
}

impl Names {
    pub fn scope(&self, scope: NodeId, kind: NsKind) -> &Scope {
        self.try_scope(scope, kind).unwrap()
    }

    pub fn try_scope(&self, scope: NodeId, kind: NsKind) -> Option<&Scope> {
        self.scopes.get(&scope).map(|s| &s[kind])
    }

    pub fn scope_mut(&mut self, scope: NodeId, kind: NsKind) -> &mut Scope {
        &mut self.scopes.entry(scope)
            .or_insert(Default::default())
            [kind]
    }

    pub fn scope_of(&self, node: NodeId) -> NodeId {
        self.node_to_scope[&node]
    }

    pub fn set_scope_of(&mut self, node: NodeId, scope: NodeId) {
        assert!(self.node_to_scope.insert(node, scope).is_none());
    }

    pub fn try_parent_scope_of(&self, scope: NodeId) -> Option<NodeId> {
        self.scope_to_parent.get(&scope).copied()
    }

    pub fn parent_of(&self, node: NodeId) -> NodeId {
        self.child_to_parent[&node]
    }

    pub fn try_parent_of(&self, node: NodeId) -> Option<NodeId> {
        self.child_to_parent.get(&node).copied()
    }

    fn set_parent_of(&mut self, child: NodeId, parent: NodeId) {
        assert!(self.child_to_parent.insert(child, parent).is_none());
    }

    pub fn module_of(&self, node: NodeId) -> NodeId {
        self.node_to_module[&node]
    }

    pub fn try_module_of(&self, node: NodeId) -> Option<NodeId> {
        self.node_to_module.get(&node).copied()
    }

    fn set_module_of(&mut self, node: NodeId, module: NodeId) {
        assert_ne!(node, module);
        assert!(self.node_to_module.insert(node, module).is_none());
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
                    if let Some(scope) = self.names.try_scope(ctx.node, kind) {
                        if !scope.is_empty() {
                            self.print_indent();
                            print!("| {:?}: ", kind);
                            for (i, (ident, ScopeItem { node, name })) in
                                scope.items.iter().enumerate()
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

struct DiscoverNames<'a> {
    names: &'a mut Names,
    /// Is in `Use` subtree?
    in_use: bool,
    scope_stack: Vec<NodeId>,
    node_stack: Vec<NodeId>,
    module_stack: Vec<NodeId>,
}

impl DiscoverNames<'_> {
    fn cur_scope(&self) -> NodeId {
        *self.scope_stack.last().unwrap()
    }

    fn insert(&mut self, ns: NsKind, name: S<Ident>, node: NodeId) {
        let scope = self.cur_scope();
        self.names.scope_mut(scope, ns).insert(name, node);
    }

    fn insert_all_namespaces(&mut self, name: S<Ident>, node: NodeId) {
        for ns in NsKind::iter() {
            self.insert(ns, name.clone(), node);
        }
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        let scope = self.cur_scope();
        for ns in NsKind::iter() {
            self.names.scope_mut(scope, ns)
                .insert_wildcard_import(node);
        }
    }
}

impl AstVisitor for DiscoverNames<'_> {
    fn before_node(&mut self, ctx: AstVisitorCtx) {
        if let Some(&parent) = self.node_stack.last() {
            self.names.set_parent_of(ctx.node, parent);
        }
        if let Some(&module) = self.module_stack.last() {
            self.names.set_module_of(ctx.node, module);
        }
        self.node_stack.push(ctx.node);

        if let Some(&scope) = self.scope_stack.last() {
            self.names.set_scope_of(ctx.node, scope);
        }

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
                self.module_stack.push(ctx.node);

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
                let name = if ident.value == Ident::self_lower() {
                    let parent = self.names.parent_of(ctx.node);
                    &ctx.ast.path_segment(parent).prefix.last().unwrap().ident
                } else {
                    renamed_as.as_ref().unwrap_or(ident)
                };
                self.insert_all_namespaces(name.clone(), ctx.node);
            }
            NodeKind::PathEndStar => {
                assert!(self.in_use);
                self.insert_wildcard_import(ctx.node);
            }
            NodeKind::Let => {},
            NodeKind::LetDecl => {
                let name = ctx.ast.let_decl(ctx.node).name.clone();
                self.insert(NsKind::Value, name, ctx.node);
            },
            NodeKind::UseStmt => {
                assert!(!self.in_use);
                self.in_use = true;
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

        if has_scope(ctx.kind) {
            self.scope_stack.push(ctx.node);
        }
    }

    fn after_node(&mut self, ctx: AstVisitorCtx) {
        if has_scope(ctx.kind) {
            loop {
                let scope = self.scope_stack.pop().unwrap();
                if let Some(parent) = self.scope_stack.last().copied() {
                    self.names.scope_to_parent.insert(scope, parent);
                }
                if scope == ctx.node {
                    break;
                }
            }
        }
        self.node_stack.pop().unwrap();
        if *self.module_stack.last().unwrap() == ctx.node {
            self.module_stack.pop().unwrap();
        }
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
            names,
            in_use: false,
            scope_stack: Vec::new(),
            node_stack: Vec::new(),
            module_stack: Vec::new(),
        },
    }.traverse();
}

fn has_scope(kind: NodeKind) -> bool {
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