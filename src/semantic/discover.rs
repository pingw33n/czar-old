use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use enum_map_derive::Enum;
use std::collections::hash_map::{Entry, HashMap};

use crate::hir::*;
use crate::hir::traverse::*;
use crate::util::enums::EnumExt;

use super::FnArgsKey;

#[derive(EnumAsInner)]
pub enum ScopeItem {
    Single {
        name: S<Ident>,
        node: NodeId,
    },
    Fns(Vec<ScopeFn>),
}

pub struct ScopeFn {
    pub name: S<Ident>,
    /// arg1:_:arg3
    pub args_key: FnArgsKey,
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
                Self::handle_conflict(e.get(), name.span);
            },
            Entry::Vacant(e) => {
                e.insert(ScopeItem::Single {
                    name,
                    node,
                });
            },
        }
    }

    pub fn insert_fn(&mut self, name: S<Ident>, args_key: FnArgsKey, node: NodeId) {
        match self.items.entry(name.value.clone()) {
            Entry::Occupied(mut e) => {
                if e.get().as_single().is_some() {
                    Self::handle_conflict(e.get(), name.span);
                }
                match e.get_mut() {
                    ScopeItem::Single { .. } => unreachable!(),
                    ScopeItem::Fns(fns) => {
                        match fns.iter().position(|s| s.args_key == args_key) {
                            Some(i) => {
                                let first = &fns[i].name;
                                let new = name.span;
                                panic!("function {}{} is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
                                    first.value, args_key, first.span.start, first.span.end, new.start, new.end);
                            }
                            None => {
                                fns.push(ScopeFn {
                                    name,
                                    args_key,
                                    node,
                                });
                            }
                        }

                    }
                }
            },
            Entry::Vacant(e) => {
                e.insert(ScopeItem::Fns(vec![ScopeFn {
                    name,
                    args_key,
                    node,
                }]));
            },
        }
    }

    fn handle_conflict(existing: &ScopeItem, new: Span) -> ! {
        let first = match existing {
            ScopeItem::Single { name, .. } => name,
            ScopeItem::Fns(fns) => &fns.first().unwrap().name,
        };
        panic!("name `{}` is defined multiple times: first at [{}:{}], redefined at [{}:{}]",
            first.value, first.span.start, first.span.end, new.start, new.end);
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
pub struct DiscoverData {
    scopes: NodeMap<EnumMap<NsKind, Scope>>,
    scope_to_parent: NodeMap<NodeId>,
    node_to_scope: NodeMap<NodeId>,
    child_to_parent: NodeMap<NodeId>,
    node_to_module: NodeMap<NodeId>,
    fn_names: NodeMap<S<Ident>>,
}

impl DiscoverData {
    pub fn build(hir: &Hir) -> Self {
        let mut data = Self::default();
        hir.traverse(&mut Build {
            data: &mut data,
            in_use: false,
            scope_stack: Vec::new(),
            node_stack: Vec::new(),
            module_stack: Vec::new(),
            fn_decl_stack: Vec::new(),
        });
        data
    }

    pub fn scope(&self, scope: NodeId, kind: NsKind) -> &Scope {
        self.try_scope(scope, kind).unwrap()
    }

    pub fn try_scope(&self, scope: NodeId, kind: NsKind) -> Option<&Scope> {
        self.scopes.get(&scope).map(|s| &s[kind])
    }

    fn scope_mut(&mut self, scope: NodeId, kind: NsKind) -> &mut Scope {
        &mut self.scopes.entry(scope)
            .or_insert(Default::default())
            [kind]
    }

    pub fn scope_of(&self, node: NodeId) -> NodeId {
        self.node_to_scope[&node]
    }

    fn set_scope_of(&mut self, node: NodeId, scope: NodeId) {
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

    pub fn set_parent_of(&mut self, child: NodeId, parent: NodeId) {
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

    pub fn fn_name(&self, node: NodeId) -> &S<Ident> {
        &self.fn_names[&node]
    }

    pub fn print_scopes(&self, hir: &Hir) {
        struct Visitor<'a> {
            data: &'a DiscoverData,
            indent: u32,
        }

        impl Visitor<'_> {
            fn print_indent(&self) {
                for _ in 1..self.indent {
                    print!("  ");
                }
            }
        }

        impl HirVisitor for Visitor<'_> {
            fn before_node(&mut self, ctx: HirVisitorCtx) {
                self.indent += 1;
                self.print_indent();
                let node = ctx.hir.node_kind(ctx.node);
                if let Some(name) = ctx.hir.try_module(ctx.node)
                    .and_then(|Module { name, .. }| name.as_ref())
                {
                    println!("{:?} {:?} `{}` {}:{}",
                        node.value, ctx.node, name.name.value, node.span.start, node.span.end);
                } else {
                    println!("{:?} {:?} {}:{}",
                        node.value, ctx.node, node.span.start, node.span.end);
                }
                for kind in NsKind::iter() {
                    if let Some(scope) = self.data.try_scope(ctx.node, kind) {
                        if !scope.is_empty() {
                            self.print_indent();
                            print!("| {:?}: ", kind);
                            for (i, (ident, scope_item)) in
                                scope.items.iter().enumerate()
                            {
                                if i > 0 {
                                    print!(", ");
                                }
                                match scope_item {
                                    ScopeItem::Single { name, node } => {
                                        let n = ctx.hir.node_kind(*node);
                                        print!("`{}` {}:{} -> {:?} {:?} {}:{}", ident,
                                            name.span.start, name.span.end,
                                            n.value, node, n.span.start, n.span.end);
                                    }
                                    ScopeItem::Fns(fns) => {
                                        for (i, ScopeFn { name, args_key: key, node }) in fns.iter().enumerate() {
                                            let n = ctx.hir.node_kind(*node);
                                            assert_eq!(n.value, NodeKind::FnDecl);
                                            if i > 0 {
                                                print!(", ");
                                            }
                                            print!("`{}::{}` {}:{} -> {:?} {:?} {}:{}",
                                                ident, key,
                                                name.span.start, name.span.end,
                                                n.value, node, n.span.start, n.span.end);
                                        }
                                    }
                                }

                            }
                            println!()
                        }
                    }
                }
            }

            fn after_node(&mut self, _ctx: HirVisitorCtx) {
                self.indent -= 1;
            }
        }

        hir.traverse(&mut Visitor {
            data: self,
            indent: 0,
        });
    }
}

struct Build<'a> {
    data: &'a mut DiscoverData,
    /// Is in `Use` subtree?
    in_use: bool,
    scope_stack: Vec<NodeId>,
    node_stack: Vec<NodeId>,
    module_stack: Vec<NodeId>,
    fn_decl_stack: Vec<NodeId>,
}

impl Build<'_> {
    fn cur_scope(&self) -> NodeId {
        *self.scope_stack.last().unwrap()
    }

    fn insert(&mut self, ns: NsKind, name: S<Ident>, node: NodeId) {
        let scope = self.cur_scope();
        self.data.scope_mut(scope, ns).insert(name, node);
    }

    fn insert_fn(&mut self, ns: NsKind, name: S<Ident>, args_key: FnArgsKey, node: NodeId) {
        let scope = self.cur_scope();
        self.data.scope_mut(scope, ns).insert_fn(name, args_key, node);
    }

    fn insert_all_namespaces(&mut self, name: S<Ident>, node: NodeId) {
        for ns in NsKind::iter() {
            self.insert(ns, name.clone(), node);
        }
    }

    fn insert_wildcard_import(&mut self, node: NodeId) {
        let scope = self.cur_scope();
        for ns in NsKind::iter() {
            self.data.scope_mut(scope, ns)
                .insert_wildcard_import(node);
        }
    }
}

impl HirVisitor for Build<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        if let Some(&parent) = self.node_stack.last() {
            self.data.set_parent_of(ctx.node, parent);
        }
        if let Some(&module) = self.module_stack.last() {
            self.data.set_module_of(ctx.node, module);
        }
        self.node_stack.push(ctx.node);

        if let Some(&scope) = self.scope_stack.last() {
            self.data.set_scope_of(ctx.node, scope);
        }

        match ctx.kind {
            NodeKind::FnDecl => {
                let name = ctx.hir.fn_decl(ctx.node).name.clone();
                let args_key = FnArgsKey::from_decl(ctx.node, ctx.hir);
                self.insert_fn(NsKind::Value, name.clone(), args_key, ctx.node);
                self.data.fn_names.insert(ctx.node, name);
                self.fn_decl_stack.push(ctx.node);
            },
            NodeKind::FnDeclArg => {
                let priv_name = ctx.hir.fn_decl_arg(ctx.node).priv_name.clone();
                self.insert(NsKind::Value, priv_name.clone(), ctx.node);
            },
            NodeKind::Let => {},
            NodeKind::LetDecl => {
                let name = ctx.hir.let_decl(ctx.node).name.clone();
                self.insert(NsKind::Value, name, ctx.node);
            },
            NodeKind::Module => {
                self.module_stack.push(ctx.node);

                let Module { name, .. } = &ctx.hir.module(ctx.node);
                if let Some(name) = name {
                    self.insert(NsKind::Type, name.name.clone(), ctx.node);
                }
            }
            NodeKind::Struct => {
                let name = ctx.hir.struct_(ctx.node).name.clone();
                self.insert(NsKind::Type, name.clone(), ctx.node);
            }
            NodeKind::PathEndIdent if self.in_use => {
                let PathEndIdent {
                    item: PathItem { ident, ty_args: _, .. },
                    renamed_as,
                } = ctx.hir.path_end_ident(ctx.node);
                let name = if ident.value == Ident::self_lower() {
                    let parent = self.data.parent_of(ctx.node);
                    &ctx.hir.path_segment(parent).prefix.last().unwrap().ident
                } else {
                    renamed_as.as_ref().unwrap_or(ident)
                };
                self.insert_all_namespaces(name.clone(), ctx.node);
            }
            NodeKind::PathEndStar => {
                assert!(self.in_use);
                self.insert_wildcard_import(ctx.node);
            }
            NodeKind::Use => {
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
            | NodeKind::StructValueField
            | NodeKind::TyExpr
            | NodeKind::TypeArg
            | NodeKind::While
            => {},
        }

        if scope_kind(ctx.kind).is_some() {
            self.scope_stack.push(ctx.node);
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        if scope_kind(ctx.kind) == Some(ScopeKind::Strong) {
            loop {
                let scope = self.scope_stack.pop().unwrap();
                if let Some(parent) = self.scope_stack.last().copied() {
                    self.data.scope_to_parent.insert(scope, parent);
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
        match ctx.kind {
            NodeKind::FnDecl => {
                assert_eq!(self.fn_decl_stack.pop().unwrap(), ctx.node);
            },
            NodeKind::Use => {
                assert!(self.in_use);
                self.in_use = false;
            },
            _ => {},
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScopeKind {
    Strong,

    /// Weak scope ends when the parent strong scope ends.
    Weak,
}

fn scope_kind(kind: NodeKind) -> Option<ScopeKind> {
    use NodeKind::*;
    match kind {
        | LetDecl
        | Path
        | PathEndEmpty
        | PathEndIdent
        | PathEndStar
        | PathSegment
        | Use
        => None,

        | Block
        | BlockFlowCtl
        | Cast
        | FieldAccess
        | FnCall
        | FnDecl
        | FnDeclArg
        | IfExpr
        | Impl
        | Literal
        | Loop
        | Module
        | Op
        | Range
        | Struct
        | StructType
        | StructValue
        | StructValueField
        | TyExpr
        | TypeArg
        | While
        => Some(ScopeKind::Strong),

        Let => Some(ScopeKind::Weak),
    }
}