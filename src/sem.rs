use enum_map::EnumMap;
use enum_map_derive::Enum;
use num_enum::{IntoPrimitive, TryFromPrimitive};
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
                // FIXME the spans are not precise
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
pub struct Namespace {
    scopes: EnumMap<NsKind, NodeMap<Scope>>,
    stack: Vec<(NodeId, Option<SourceId>)>,
}

impl Namespace {
    pub fn push(&mut self, node: NodeId, source_id: Option<SourceId>) {
        self.stack.push((node, source_id));
    }

    pub fn pop_until(&mut self, node: NodeId) {
        while self.stack.pop().unwrap().0 != node { }
    }

    pub fn scope_mut(&mut self, kind: NsKind) -> &mut Scope {
        let &(node, _) = self.stack.last().unwrap();
        self.scopes[kind].entry(node)
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
}

pub struct AstVisitorCtx<'a> {
    pub ast: &'a Ast,
    pub namespace: &'a mut Namespace,
}

pub trait AstVisitor {
    fn before_node(&mut self, node: NodeId, kind: NodeKind, ctx: AstVisitorCtx);
    fn node(&mut self, node: NodeId, kind: NodeKind, ctx: AstVisitorCtx);
}

pub struct AstTraverser<'a, T> {
    pub ast: &'a Ast,
    pub namespace: &'a mut Namespace,
    pub visitor: &'a mut T,
}

impl<T: AstVisitor> AstTraverser<'_, T> {
    pub fn traverse(&mut self) {
        let source_id = self.ast.module_decl(self.ast.root).source_id;
        self.namespace.push(self.ast.root, source_id);
        self.traverse0(self.ast.root);
        self.namespace.pop_until(self.ast.root);
    }

    fn before_node(&mut self, node: NodeId, kind: NodeKind) {
        self.visitor.before_node(node, kind, AstVisitorCtx {
            ast: self.ast,
            namespace: self.namespace,
        });
    }

    fn node(&mut self, node: NodeId, kind: NodeKind) {
        self.visitor.node(node, kind, AstVisitorCtx {
            ast: self.ast,
            namespace: self.namespace,
        });
    }

    fn traverse0(&mut self, node: NodeId) {
        let kind = self.ast.node_kind(node).value;
        self.before_node(node, kind);

        let source_id = if kind == NodeKind::ModuleDecl {
            self.ast.module_decl(node).source_id
        } else {
            None
        };
        self.namespace.push(node, source_id);
        self.node(node, kind);

        match kind {
            NodeKind::Block => {
                let Block { exprs, .. } = self.ast.block(node);
                for &expr in exprs {
                    self.traverse0(expr);
                }
            },
            NodeKind::BlockFlowCtl => {
                let BlockFlowCtl { value, .. } = self.ast.block_flow_ctl(node);
                if let &Some(value) = value {
                    self.traverse0(value);
                }
            },
            NodeKind::Cast => {
                let Cast { expr, ty, .. } = self.ast.cast(node);
                self.traverse0(*expr);
                self.traverse0(*ty);
            },
            NodeKind::FieldAccess => {
                let FieldAccess { receiver, .. } = self.ast.field_access(node);
                self.traverse0(*receiver);
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
                    self.traverse0(ty_arg);
                }
                for &arg in args {
                    self.traverse0(arg);
                }
                if let &Some(ret_ty) = ret_ty {
                    self.traverse0(ret_ty);
                }
                if let &Some(body) = body {
                    self.traverse0(body);
                }
            },
            NodeKind::FnDeclArg => {
                let &FnDeclArg { ty, .. } = self.ast.fn_decl_arg(node);
                self.traverse0(ty);
            },
            NodeKind::FnCall => {
                let FnCall { callee, args, .. } = self.ast.fn_call(node);
                self.traverse0(*callee);
                for arg in args {
                    self.traverse0(arg.value);
                }
            },
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false, .. } = self.ast.if_expr(node);
                self.traverse0(cond);
                self.traverse0(if_true);

                if let Some(if_false) = if_false {
                    self.traverse0(if_false);
                }
            },
            NodeKind::Impl => {
                let Impl { ty_args, items, .. } = self.ast.impl_(node);
                for &ty_arg in ty_args {
                    self.traverse0(ty_arg);
                }
                for &item in items {
                    self.traverse0(item);
                }
            },
            NodeKind::Literal => {},
            NodeKind::Loop => {
                let &Loop { block, .. } = self.ast.loop_(node);
                self.traverse0(block);
            },
            NodeKind::ModuleDecl => {
                let ModuleDecl { items, .. } = self.ast.module_decl(node);
                for &item in items {
                    self.traverse0(item);
                }
            },
            NodeKind::Op => {
                match self.ast.op(node) {
                    &Op::Binary(BinaryOp { left, right, .. }) => {
                        self.traverse0(left);
                        self.traverse0(right);
                    }
                    &Op::Unary(UnaryOp { arg, .. }) => {
                        self.traverse0(arg);
                    }
                }
            },
            NodeKind::Range => {
                let &Range { start, end, .. } = self.ast.range(node);
                if let Some(start) = start {
                    self.traverse0(start);
                }
                if let Some(end) = end {
                    self.traverse0(end);
                }
            },
            NodeKind::StructDecl => {
                let StructDecl { ty_args, ty, .. } = self.ast.struct_decl(node);
                for &ty_arg in ty_args {
                    self.traverse0(ty_arg);
                }
                self.traverse0(*ty);
            },
            NodeKind::StructType => {
                let StructType { fields, .. } = self.ast.struct_type(node);
                for &StructTypeField { ty, .. } in fields {
                    self.traverse0(ty);
                }
            },
            NodeKind::StructValue => {
                let StructValue { fields, .. } = self.ast.struct_value(node);
                for &StructValueField { value, .. } in fields {
                    self.traverse0(value);
                }
            },
            NodeKind::SymPath => {
                let SymPath { items, .. } = self.ast.sym_path(node);
                for PathItem{ ty_args, .. } in items {
                    for &ty_arg in ty_args {
                        self.traverse0(ty_arg);
                    }
                }
            },
            NodeKind::TyExpr => {
                let TyExpr { data, .. } = self.ast.ty_expr(node);
                match &data.value {
                    &TyData::Array(Array { ty, len }) => {
                        self.traverse0(ty);
                        self.traverse0(len);
                    },
                    | &TyData::Ptr(n)
                    | &TyData::Ref(n)
                    | &TyData::SymPath(n)
                    | &TyData::Struct(n)
                    | &TyData::Slice(Slice { ty: n, .. })
                    => {
                        self.traverse0(n);
                    },
                }
            },
            NodeKind::TypeArg => {},
            NodeKind::UseStmt => {
                let UseStmt { path , ..} = self.ast.use_stmt(node);
                self.traverse0(path.value.path);
            },
            NodeKind::UsePath => {
                let UsePath { terms, .. } = self.ast.use_path(node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(..) => {},
                        &PathTerm::Path(n) => self.traverse0(n),
                        PathTerm::Star => {},
                    }
                }
            },
            NodeKind::VarDecl => {
                let &VarDecl { ty, init, .. } = self.ast.var_decl(node);
                if let Some(ty) = ty {
                    self.traverse0(ty);
                }
                if let Some(init) = init {
                    self.traverse0(init);
                }
            },
            NodeKind::While => {
                let &While { cond, block, .. } = self.ast.while_(node);
                self.traverse0(cond);
                self.traverse0(block);
            },
        }
        self.namespace.pop_until(node);
    }
}

pub struct DiscoverNames;

impl AstVisitor for DiscoverNames {
    fn before_node(&mut self, node: NodeId, kind: NodeKind, mut ctx: AstVisitorCtx) {
        match kind {
            NodeKind::FnDecl => {
                let name = ctx.ast.fn_decl(node).name.clone();
                ctx.namespace.scope_mut(NsKind::Value).insert(name, node);
            },
            NodeKind::FnDeclArg => {
                let FnDeclArg { pub_name, priv_name, ty: _ } = ctx.ast.fn_decl_arg(node);

                let pub_name = pub_name.value.as_ref()
                    .map(|v| pub_name.span.spanned(v.clone()))
                    .unwrap_or_else(|| priv_name.clone());
                ctx.namespace.scope_mut(NsKind::Misc).insert(pub_name, node);

                ctx.namespace.scope_mut(NsKind::Value).insert(priv_name.clone(), node);
            },
            NodeKind::ModuleDecl => {
                let ModuleDecl { source_id: _, name, items } = ctx.ast.module_decl(node);
                if let Some(name) = name {
                    ctx.namespace.scope_mut(NsKind::Type).insert(name.name.clone(), node);
                }
            }
            NodeKind::StructDecl => {
                let name = ctx.ast.struct_decl(node).name.clone();
                ctx.namespace.scope_mut(NsKind::Type).insert(name.clone(), node);
            }
            NodeKind::UsePath => {
                let UsePath { terms, .. } = ctx.ast.use_path(node);
                for term in terms {
                    match &term.value {
                        PathTerm::Ident(PathTermIdent { ident, renamed_as }) => {
                            let name = renamed_as.as_ref()
                                .unwrap_or(ident)
                                .clone();
                            ctx.namespace.scope_mut(NsKind::Type).insert(name, node);
                        },
                        &PathTerm::Path(v) => {},
                        PathTerm::Star => {
                            ctx.namespace.scope_mut(NsKind::Type).insert_wildcarded(node);
                        },
                    }
                }
            },
            NodeKind::VarDecl => {
                let name = ctx.ast.var_decl(node).name.clone();
                ctx.namespace.scope_mut(NsKind::Value).insert(name, node);
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

    fn node(&mut self, node: NodeId, kind: NodeKind, ctx: AstVisitorCtx) {
    }
}

pub struct Context<'a> {
    pub packages: Slab<Package>,
    pub package_by_name: HashMap<Ident, PackageId>,
    pub ast: &'a Ast,
}
