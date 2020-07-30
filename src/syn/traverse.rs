use super::*;

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
    Let(LetLink),
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
pub enum LetLink {
    Decl,
    Type,
    Init,
}

#[derive(Clone, Copy, Debug)]
pub enum WhileLink {
    Cond,
    Block,
}

#[derive(Clone, Copy)]
pub struct AstVisitorCtx<'a> {
    pub node: NodeId,
    pub kind: NodeKind,
    pub link_kind: NodeLinkKind,
    pub ast: &'a Ast,
}

pub trait AstVisitor {
    fn before_node(&mut self, _ctx: AstVisitorCtx) {}
    fn node(&mut self, _ctx: AstVisitorCtx) {}
    fn after_node(&mut self, _ctx: AstVisitorCtx) {}
}

pub struct AstTraverser<'a, T> {
    pub ast: &'a Ast,
    pub visitor: &'a mut T,
}

impl<T: AstVisitor> AstTraverser<'_, T> {
    pub fn traverse(&mut self) {
        self.traverse_from(self.ast.root);
    }

    pub fn traverse_from(&mut self, node: NodeId) {
        self.traverse0(node, NodeLinkKind::Root);
    }

    fn before_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind) {
        self.visitor.before_node(AstVisitorCtx { node, kind, link_kind, ast: self.ast });
    }

    fn node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind) {
        self.visitor.node(AstVisitorCtx { node, kind, link_kind, ast: self.ast });
    }

    fn after_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLinkKind) {
        self.visitor.after_node(AstVisitorCtx { node, kind, link_kind, ast: self.ast });
    }

    fn traverse0(&mut self, node: NodeId, link_kind: NodeLinkKind) {
        let kind = self.ast.node_kind(node).value;
        self.before_node(node, kind, link_kind);
        self.node(node, kind, link_kind);

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
            NodeKind::Let => {
                let &Let { decl } = self.ast.let_(node);
                self.traverse0(decl, NodeLinkKind::Let(LetLink::Decl));
            }
            NodeKind::LetDecl => {
                let &LetDecl { ty, init, .. } = self.ast.let_decl(node);
                if let Some(ty) = ty {
                    self.traverse0(ty, NodeLinkKind::Let(LetLink::Type));
                }
                if let Some(init) = init {
                    self.traverse0(init, NodeLinkKind::Let(LetLink::Init));
                }
            },
            NodeKind::While => {
                let &While { cond, block, .. } = self.ast.while_(node);
                self.traverse0(cond, NodeLinkKind::While(WhileLink::Cond));
                self.traverse0(block, NodeLinkKind::While(WhileLink::Block));
            },
        }
        self.after_node(node, kind, link_kind);
    }
}