use super::*;

impl Hir {
    pub fn traverse(&self, visitor: &mut impl HirVisitor) {
        self.traverse_from(self.root, visitor);
    }

    pub fn traverse_from(&self, node: NodeId, visitor: &mut impl HirVisitor) {
        Traverser {
            hir: self,
            visitor,
        }.traverse(node);
    }
}

#[derive(Clone, Copy, Debug)]
pub enum NodeLink {
    BlockExpr,
    BlockFlowCtlValue,
    Cast(CastLink),
    FieldAccessReceiver,
    FnCall(FnCallLink),
    Fn(FnLink),
    FnDeclArgType,
    IfExpr(IfExprLink),
    Impl(ImplLink),
    LoopBlock,
    ModuleItem,
    Op(OpLink),
    Path(PathLink),
    Range(RangeLink),
    Root,
    StructDecl(StructDeclLink),
    StructTypeFieldType,
    StructValueValue,
    TyExpr(TyExprLink),
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
pub enum FnLink {
    Decl,
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

#[derive(Clone, Copy, Debug)]
pub enum PathLink {
    Segment,
    SegmentSuffix,
    SegmentItemTyArgs,
    EndIdentTyArgs,
}

#[derive(Clone, Copy)]
pub struct HirVisitorCtx<'a> {
    pub node: NodeId,
    pub kind: NodeKind,
    pub link: NodeLink,
    pub hir: &'a Hir,
}

pub trait HirVisitor {
    fn before_node(&mut self, _ctx: HirVisitorCtx) {}
    fn after_node(&mut self, _ctx: HirVisitorCtx) {}
}

struct Traverser<'a, T> {
    pub hir: &'a Hir,
    pub visitor: &'a mut T,
}

impl<T: HirVisitor> Traverser<'_, T> {
    pub fn traverse(&mut self, node: NodeId) {
        self.traverse0(node, NodeLink::Root);
    }

    fn before_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLink) {
        self.visitor.before_node(HirVisitorCtx { node, kind, link: link_kind, hir: self.hir });
    }

    fn after_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLink) {
        self.visitor.after_node(HirVisitorCtx { node, kind, link: link_kind, hir: self.hir });
    }

    fn traverse0(&mut self, node: NodeId, link_kind: NodeLink) {
        let kind = self.hir.node_kind(node).value;
        self.before_node(node, kind, link_kind);

        match kind {
            NodeKind::Block => {
                let Block { exprs, .. } = self.hir.block(node);
                for &expr in exprs {
                    self.traverse0(expr, NodeLink::BlockExpr);
                }
            },
            NodeKind::BlockFlowCtl => {
                let BlockFlowCtl { value, .. } = self.hir.block_flow_ctl(node);
                if let &Some(value) = value {
                    self.traverse0(value, NodeLink::BlockFlowCtlValue);
                }
            },
            NodeKind::Cast => {
                let Cast { expr, ty, .. } = self.hir.cast(node);
                self.traverse0(*expr, NodeLink::Cast(CastLink::Expr));
                self.traverse0(*ty, NodeLink::Cast(CastLink::Type));
            },
            NodeKind::FieldAccess => {
                let FieldAccess { receiver, .. } = self.hir.field_access(node);
                self.traverse0(*receiver, NodeLink::FieldAccessReceiver);
            },
            NodeKind::FnCall => {
                let FnCall { callee, args, .. } = self.hir.fn_call(node);
                self.traverse0(*callee, NodeLink::FnCall(FnCallLink::Callee));
                for arg in args {
                    self.traverse0(arg.value, NodeLink::FnCall(FnCallLink::ArgValue));
                }
            },
            NodeKind::FnDecl => {
                let FnDecl {
                    ty_args,
                    args,
                    ret_ty,
                    body,
                    ..
                } = self.hir.fn_decl(node);

                for &ty_arg in ty_args {
                    self.traverse0(ty_arg, NodeLink::Fn(FnLink::TypeArg));
                }
                for &arg in args {
                    self.traverse0(arg, NodeLink::Fn(FnLink::Arg));
                }
                if let &Some(ret_ty) = ret_ty {
                    self.traverse0(ret_ty, NodeLink::Fn(FnLink::RetType));
                }
                if let &Some(body) = body {
                    self.traverse0(body, NodeLink::Fn(FnLink::Body));
                }
            },
            NodeKind::FnDeclArg => {
                let &FnDeclArg { ty, .. } = self.hir.fn_decl_arg(node);
                self.traverse0(ty, NodeLink::FnDeclArgType);
            },
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false, .. } = self.hir.if_expr(node);
                self.traverse0(cond, NodeLink::IfExpr(IfExprLink::Cond));
                self.traverse0(if_true, NodeLink::IfExpr(IfExprLink::IfTrue));

                if let Some(if_false) = if_false {
                    self.traverse0(if_false, NodeLink::IfExpr(IfExprLink::IfFalse));
                }
            },
            NodeKind::Impl => {
                let Impl { ty_args, items, .. } = self.hir.impl_(node);
                for &ty_arg in ty_args {
                    self.traverse0(ty_arg, NodeLink::Impl(ImplLink::TypeArg));
                }
                for &item in items {
                    self.traverse0(item, NodeLink::Impl(ImplLink::Item));
                }
            },
            NodeKind::Let => {
                let &Let { decl } = self.hir.let_(node);
                self.traverse0(decl, NodeLink::Let(LetLink::Decl));
            }
            NodeKind::LetDecl => {
                let &LetDecl { ty, init, .. } = self.hir.let_decl(node);
                if let Some(ty) = ty {
                    self.traverse0(ty, NodeLink::Let(LetLink::Type));
                }
                if let Some(init) = init {
                    self.traverse0(init, NodeLink::Let(LetLink::Init));
                }
            },
            NodeKind::Literal => {},
            NodeKind::Loop => {
                let &Loop { block, .. } = self.hir.loop_(node);
                self.traverse0(block, NodeLink::LoopBlock);
            },
            NodeKind::Module => {
                let Module { items, .. } = self.hir.module(node);
                for &item in items {
                    self.traverse0(item, NodeLink::ModuleItem);
                }
            },
            NodeKind::Op => {
                match self.hir.op(node) {
                    &Op::Binary(BinaryOp { left, right, .. }) => {
                        self.traverse0(left, NodeLink::Op(OpLink::BinaryLeft));
                        self.traverse0(right, NodeLink::Op(OpLink::BinaryRight));
                    }
                    &Op::Unary(UnaryOp { arg, .. }) => {
                        self.traverse0(arg, NodeLink::Op(OpLink::UnaryArg));
                    }
                }
            },
            NodeKind::Range => {
                let &Range { start, end, .. } = self.hir.range(node);
                if let Some(start) = start {
                    self.traverse0(start, NodeLink::Range(RangeLink::Start));
                }
                if let Some(end) = end {
                    self.traverse0(end, NodeLink::Range(RangeLink::End));
                }
            },
            NodeKind::Struct => {
                let Struct { ty_args, ty, .. } = self.hir.struct_(node);
                for &ty_arg in ty_args {
                    self.traverse0(ty_arg, NodeLink::StructDecl(StructDeclLink::TypeArg));
                }
                self.traverse0(*ty, NodeLink::StructDecl(StructDeclLink::Type));
            },
            NodeKind::StructType => {
                let StructType { fields, .. } = self.hir.struct_type(node);
                for &StructTypeField { ty, .. } in fields {
                    self.traverse0(ty, NodeLink::StructTypeFieldType);
                }
            },
            NodeKind::StructValue => {
                let StructValue { fields, .. } = self.hir.struct_value(node);
                for &StructValueField { value, .. } in fields {
                    self.traverse0(value, NodeLink::StructValueValue);
                }
            },
            NodeKind::Path => {
                let &Path { anchor: _, segment } = self.hir.path(node);
                self.traverse0(segment, NodeLink::Path(PathLink::Segment));
            },
            NodeKind::PathEndEmpty => {},
            NodeKind::PathEndIdent => {
                let PathEndIdent {
                    item: PathItem { ident: _, ty_args },
                    renamed_as: _,
                } = self.hir.path_end_ident(node);
                for &node in ty_args {
                    self.traverse0(node, NodeLink::Path(PathLink::EndIdentTyArgs));
                }
            },
            NodeKind::PathEndStar => {},
            NodeKind::PathSegment => {
                let PathSegment { prefix, suffix } = self.hir.path_segment(node);
                for PathItem { ident: _, ty_args } in prefix {
                    for &node in ty_args {
                        self.traverse0(node, NodeLink::Path(PathLink::SegmentItemTyArgs));
                    }
                }
                for &node in suffix {
                    self.traverse0(node, NodeLink::Path(PathLink::SegmentSuffix));
                }
            },
            NodeKind::TyExpr => {
                let TyExpr { data, .. } = self.hir.ty_expr(node);
                match &data.value {
                    &TyData::Array(Array { ty, len }) => {
                        self.traverse0(ty, NodeLink::TyExpr(TyExprLink::Array(ArrayLink::Type)));
                        self.traverse0(len, NodeLink::TyExpr(TyExprLink::Array(ArrayLink::Len)));
                    },
                    &TyData::Ptr(n) => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Ptr)),
                    &TyData::Ref(n) => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Ref)),
                    &TyData::Path(n) => self.traverse0(n, NodeLink::TyExpr(TyExprLink::SymPath)),
                    &TyData::Struct(n)  => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Struct)),
                    &TyData::Slice(Slice { ty: n, .. }) => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Slice)),
                }
            },
            NodeKind::TypeArg => {},
            NodeKind::UseStmt => {
                let UseStmt { path , ..} = self.hir.use_stmt(node);
                self.traverse0(*path, NodeLink::UseStmtPath);
            },
            NodeKind::While => {
                let &While { cond, block, .. } = self.hir.while_(node);
                self.traverse0(cond, NodeLink::While(WhileLink::Cond));
                self.traverse0(block, NodeLink::While(WhileLink::Block));
            },
        }
        self.after_node(node, kind, link_kind);
    }
}