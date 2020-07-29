use enum_map::EnumMap;
use enum_map_derive::Enum;
use slab::Slab;
use std::collections::hash_map::{Entry, HashMap};

use crate::syn::*;
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

pub struct AstVisitorCtx<'a> {
    pub ast: &'a Ast,
    pub names: &'a mut Names,
}

#[derive(Clone, Copy, Debug)]
pub enum NodeLinkKind {
    BlockExpr,
    BlockFlowCtlValue,
    Cast(CastLink),
    FieldAccessReceiver,
    FnCall(FnCallLink),
    FnDecl(FnDeclLink),
    FnDeclArgType,
    IfExpr(IfExprLink),
    Impl(ImplLink),
    LoopBlock,
    ModuleItem,
    Op(OpLink),
    Range(RangeLink),
    Root,
    StructDecl(StructDeclLink),
    StructTypeFieldType,
    StructValueValue,
    SymPathTypeArg,
    TyExpr(TyExprLink),
    UsePathPath,
    UseStmtPath,
    VarDecl(VarDeclLink),
    While(WhileLink),
}

#[derive(Clone, Copy, Debug)]
pub enum CastLink {
    Expr,
    Type,
}

#[derive(Clone, Copy, Debug)]
pub enum FnDeclLink {
    TypeArg,
    Arg,
    RetType,
    Body,
}

#[derive(Clone, Copy, Debug)]
pub enum FnCallLink {
    Callee,
    ArgValue,
}

#[derive(Clone, Copy, Debug)]
pub enum IfExprLink {
    Cond,
    IfTrue,
    IfFalse,
}

#[derive(Clone, Copy, Debug)]
pub enum ImplLink {
    TypeArg,
    Item,
}

#[derive(Clone, Copy, Debug)]
pub enum OpLink {
    BinaryLeft,
    BinaryRight,
    UnaryArg,
}

#[derive(Clone, Copy, Debug)]
pub enum RangeLink {
    Start,
    End,
}

#[derive(Clone, Copy, Debug)]
pub enum StructDeclLink {
    Type,
    TypeArg,
}

#[derive(Clone, Copy, Debug)]
pub enum TyExprLink {
    Array(ArrayLink),
    Ptr,
    Ref,
    SymPath,
    Struct,
    Slice,
}

#[derive(Clone, Copy, Debug)]
pub enum ArrayLink {
    Type,
    Len,
}

#[derive(Clone, Copy, Debug)]
pub enum VarDeclLink {
    Type,
    Init,
}

#[derive(Clone, Copy, Debug)]
pub enum WhileLink {
    Cond,
    Block,
}

pub trait AstVisitor {
    fn before_node(&mut self,
        _node: NodeId,
        _kind: NodeKind,
        _link_kind: NodeLinkKind,
        _ctx: AstVisitorCtx,
    ) {}

    fn node(&mut self,
        _node: NodeId,
        _kind: NodeKind,
        _link_kind: NodeLinkKind,
        _ctx: AstVisitorCtx,
    ) {}

    fn after_node(&mut self,
        _node: NodeId,
        _kind: NodeKind,
        _link_kind: NodeLinkKind,
        _ctx: AstVisitorCtx,
    ) {}
}

pub struct AstTraverser<'a, T> {
    pub ast: &'a Ast,
    pub names: &'a mut Names,
    pub visitor: &'a mut T,
}

impl<T: AstVisitor> AstTraverser<'_, T> {
    pub fn traverse(&mut self) {
        let source_id = self.ast.module_decl(self.ast.root).source_id;
        self.names.push(self.ast.root, source_id);
        self.traverse0(self.ast.root, NodeLinkKind::Root);
        self.names.pop_until(self.ast.root);
    }

    fn before_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind) {
        self.visitor.before_node(node, kind, link_kind, AstVisitorCtx {
            ast: self.ast,
            names: self.names,
        });
    }

    fn node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind) {
        self.visitor.node(node, kind, link_kind, AstVisitorCtx {
            ast: self.ast,
            names: self.names,
        });
    }

    fn after_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind) {
        self.visitor.after_node(node, kind, link_kind, AstVisitorCtx {
            ast: self.ast,
            names: self.names,
        });
    }

    fn traverse0(&mut self, node: NodeId, link_kind: NodeLinkKind) {
        let kind = self.ast.node_kind(node).value;
        self.before_node(node, kind, link_kind);

        let source_id = if kind == NodeKind::ModuleDecl {
            self.ast.module_decl(node).source_id
        } else {
            None
        };
        self.names.push(node, source_id);
        self.node(node, kind, link_kind);

        let mut pop_scope = true;

        match kind {
            NodeKind::Block => {
                let Block { exprs, .. } = self.ast.block(node);
                for &expr in exprs {
                    self.traverse0(expr, NodeLinkKind::BlockExpr);
                }
            },
            NodeKind::BlockFlowCtl => {
                let BlockFlowCtl { value, .. } = self.ast.block_flow_ctl(node);
                if let &Some(value) = value {
                    self.traverse0(value, NodeLinkKind::BlockFlowCtlValue);
                }
            },
            NodeKind::Cast => {
                let Cast { expr, ty, .. } = self.ast.cast(node);
                self.traverse0(*expr, NodeLinkKind::Cast(CastLink::Expr));
                self.traverse0(*ty, NodeLinkKind::Cast(CastLink::Type));
            },
            NodeKind::FieldAccess => {
                let FieldAccess { receiver, .. } = self.ast.field_access(node);
                self.traverse0(*receiver, NodeLinkKind::FieldAccessReceiver);
            },
            NodeKind::FnCall => {
                let FnCall { callee, args, .. } = self.ast.fn_call(node);
                self.traverse0(*callee, NodeLinkKind::FnCall(FnCallLink::Callee));
                for arg in args {
                    self.traverse0(arg.value, NodeLinkKind::FnCall(FnCallLink::ArgValue));
                }
            },
            NodeKind::FnDecl => {
                let FnDecl {
                    ty_args,
                    args,
                    ret_ty,
                    body,
                    ..
                } = self.ast.fn_decl(node);

                for &ty_arg in ty_args {
                    self.traverse0(ty_arg, NodeLinkKind::FnDecl(FnDeclLink::TypeArg));
                }
                for &arg in args {
                    self.traverse0(arg, NodeLinkKind::FnDecl(FnDeclLink::Arg));
                }
                if let &Some(ret_ty) = ret_ty {
                    self.traverse0(ret_ty, NodeLinkKind::FnDecl(FnDeclLink::RetType));
                }
                if let &Some(body) = body {
                    self.traverse0(body, NodeLinkKind::FnDecl(FnDeclLink::Body));
                }
            },
            NodeKind::FnDeclArg => {
                let &FnDeclArg { ty, .. } = self.ast.fn_decl_arg(node);
                self.traverse0(ty, NodeLinkKind::FnDeclArgType);
            },
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false, .. } = self.ast.if_expr(node);
                self.traverse0(cond, NodeLinkKind::IfExpr(IfExprLink::Cond));
                self.traverse0(if_true, NodeLinkKind::IfExpr(IfExprLink::IfTrue));

                if let Some(if_false) = if_false {
                    self.traverse0(if_false, NodeLinkKind::IfExpr(IfExprLink::IfFalse));
                }
            },
            NodeKind::Impl => {
                let Impl { ty_args, items, .. } = self.ast.impl_(node);
                for &ty_arg in ty_args {
                    self.traverse0(ty_arg, NodeLinkKind::Impl(ImplLink::TypeArg));
                }
                for &item in items {
                    self.traverse0(item, NodeLinkKind::Impl(ImplLink::Item));
                }
            },
            NodeKind::Literal => {},
            NodeKind::Loop => {
                let &Loop { block, .. } = self.ast.loop_(node);
                self.traverse0(block, NodeLinkKind::LoopBlock);
            },
            NodeKind::ModuleDecl => {
                let ModuleDecl { items, .. } = self.ast.module_decl(node);
                for &item in items {
                    self.traverse0(item, NodeLinkKind::ModuleItem);
                }
            },
            NodeKind::Op => {
                match self.ast.op(node) {
                    &Op::Binary(BinaryOp { left, right, .. }) => {
                        self.traverse0(left, NodeLinkKind::Op(OpLink::BinaryLeft));
                        self.traverse0(right, NodeLinkKind::Op(OpLink::BinaryRight));
                    }
                    &Op::Unary(UnaryOp { arg, .. }) => {
                        self.traverse0(arg, NodeLinkKind::Op(OpLink::UnaryArg));
                    }
                }
            },
            NodeKind::Range => {
                let &Range { start, end, .. } = self.ast.range(node);
                if let Some(start) = start {
                    self.traverse0(start, NodeLinkKind::Range(RangeLink::Start));
                }
                if let Some(end) = end {
                    self.traverse0(end, NodeLinkKind::Range(RangeLink::End));
                }
            },
            NodeKind::StructDecl => {
                let StructDecl { ty_args, ty, .. } = self.ast.struct_decl(node);
                for &ty_arg in ty_args {
                    self.traverse0(ty_arg, NodeLinkKind::StructDecl(StructDeclLink::TypeArg));
                }
                self.traverse0(*ty, NodeLinkKind::StructDecl(StructDeclLink::Type));
            },
            NodeKind::StructType => {
                let StructType { fields, .. } = self.ast.struct_type(node);
                for &StructTypeField { ty, .. } in fields {
                    self.traverse0(ty, NodeLinkKind::StructTypeFieldType);
                }
            },
            NodeKind::StructValue => {
                let StructValue { fields, .. } = self.ast.struct_value(node);
                for &StructValueField { value, .. } in fields {
                    self.traverse0(value, NodeLinkKind::StructValueValue);
                }
            },
            NodeKind::SymPath => {
                let SymPath { items, .. } = self.ast.sym_path(node);
                for PathItem{ ty_args, .. } in items {
                    for &ty_arg in ty_args {
                        self.traverse0(ty_arg, NodeLinkKind::SymPathTypeArg);
                    }
                }
            },
            NodeKind::TyExpr => {
                let TyExpr { data, .. } = self.ast.ty_expr(node);
                match &data.value {
                    &TyData::Array(Array { ty, len }) => {
                        self.traverse0(ty, NodeLinkKind::TyExpr(TyExprLink::Array(ArrayLink::Type)));
                        self.traverse0(len, NodeLinkKind::TyExpr(TyExprLink::Array(ArrayLink::Len)));
                    },
                    &TyData::Ptr(n) => self.traverse0(n, NodeLinkKind::TyExpr(TyExprLink::Ptr)),
                    &TyData::Ref(n) => self.traverse0(n, NodeLinkKind::TyExpr(TyExprLink::Ref)),
                    &TyData::SymPath(n) => self.traverse0(n, NodeLinkKind::TyExpr(TyExprLink::SymPath)),
                    &TyData::Struct(n)  => self.traverse0(n, NodeLinkKind::TyExpr(TyExprLink::Struct)),
                    &TyData::Slice(Slice { ty: n, .. }) => self.traverse0(n, NodeLinkKind::TyExpr(TyExprLink::Slice)),
                }
            },
            NodeKind::TypeArg => {},
            NodeKind::UsePath => {
                let UsePath { terms, .. } = self.ast.use_path(node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(..) => {},
                        &PathTerm::Path(n) => self.traverse0(n, NodeLinkKind::UsePathPath),
                        PathTerm::Star => {},
                    }
                }
            },
            NodeKind::UseStmt => {
                let UseStmt { path , ..} = self.ast.use_stmt(node);
                self.traverse0(path.value.path, NodeLinkKind::UseStmtPath);
            },
            NodeKind::VarDecl => {
                let &VarDecl { ty, init, .. } = self.ast.var_decl(node);
                if let Some(ty) = ty {
                    self.traverse0(ty, NodeLinkKind::VarDecl(VarDeclLink::Type));
                }
                if let Some(init) = init {
                    self.names.push(init, None);
                    self.traverse0(init, NodeLinkKind::VarDecl(VarDeclLink::Init));
                    self.names.pop_until(init);
                }
                pop_scope = false;
            },
            NodeKind::While => {
                let &While { cond, block, .. } = self.ast.while_(node);
                self.traverse0(cond, NodeLinkKind::While(WhileLink::Cond));
                self.traverse0(block, NodeLinkKind::While(WhileLink::Block));
            },
        }
        if pop_scope {
            self.names.pop_until(node);
        }
        self.after_node(node, kind, link_kind);
    }
}

pub struct DiscoverNames;

impl AstVisitor for DiscoverNames {
    fn before_node(&mut self, node: NodeId, kind: NodeKind, _link_kind: NodeLinkKind, ctx: AstVisitorCtx) {
        match kind {
            NodeKind::FnDecl => {
                let name = ctx.ast.fn_decl(node).name.clone();
                ctx.names.scope_mut(NsKind::Value).insert(name, node);
            },
            NodeKind::FnDeclArg => {
                let FnDeclArg { pub_name, priv_name, ty: _ } = ctx.ast.fn_decl_arg(node);

                let pub_name = pub_name.value.as_ref()
                    .map(|v| pub_name.span.spanned(v.clone()))
                    .unwrap_or_else(|| priv_name.clone());
                ctx.names.scope_mut(NsKind::Misc).insert(pub_name, node);

                ctx.names.scope_mut(NsKind::Value).insert(priv_name.clone(), node);
            },
            NodeKind::ModuleDecl => {
                let name = &ctx.ast.module_decl(node).name;
                if let Some(name) = name {
                    ctx.names.scope_mut(NsKind::Type).insert(name.name.clone(), node);
                }
            }
            NodeKind::StructDecl => {
                let name = ctx.ast.struct_decl(node).name.clone();
                ctx.names.scope_mut(NsKind::Type).insert(name.clone(), node);
            }
            NodeKind::UsePath => {
                let UsePath { terms, .. } = ctx.ast.use_path(node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(PathTermIdent { ident, renamed_as }) => {
                            let name = renamed_as.as_ref()
                                .unwrap_or(ident);
                            for &ns_kind in &[NsKind::Type, NsKind::Value] {
                                ctx.names.scope_mut(ns_kind).insert(name.clone(), node);
                            }
                        },
                        &PathTerm::Path(_) => {},
                        PathTerm::Star => {
                            for &ns_kind in &[NsKind::Type, NsKind::Value] {
                                ctx.names.scope_mut(ns_kind).insert_wildcarded(node);
                            }
                        },
                    }
                }
            },
            NodeKind::VarDecl => {
                let name = ctx.ast.var_decl(node).name.clone();
                ctx.names.scope_mut(NsKind::Value).insert(name, node);
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
    }
}

pub struct Context<'a> {
    pub packages: Slab<Package>,
    pub package_by_name: HashMap<Ident, PackageId>,
    pub ast: &'a Ast,
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
    resolved_names: &'a mut ResolvedNames,
    ns_kind_stack: Vec<NsKind>,
}

impl<'a> ResolveNames<'a> {
    pub fn new(resolved_names: &'a mut ResolvedNames) -> Self {
        Self {
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
    fn node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind, ctx: AstVisitorCtx) {
        self.push_ns_kind(link_kind);

        match kind {
            NodeKind::SymPath => {
                let SymPath { anchor, items } = ctx.ast.sym_path(node);
                if anchor.is_some() {
                    unimplemented!();
                }
                let first = &items[0].ident;
                let ns_kind = *self.ns_kind_stack.last().unwrap();
                if let Some(resolved) = ctx.names.resolve(ns_kind, &first.value) {
                    if items.len() > 1 {
                        unimplemented!();
                    }
                    self.resolved_names.insert(ns_kind, node, resolved);
                } else {
                    eprintln!("[{}:{}] couldn't find name `{}` in the current scope",
                        first.span.start, first.span.end, first.value);
                }
            }
            _ => {}
        }
    }

    fn after_node(&mut self, _: NodeId, _: NodeKind, _: NodeLinkKind, _: AstVisitorCtx) {
        self.ns_kind_stack.pop().unwrap();
    }
}