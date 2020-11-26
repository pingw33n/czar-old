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
    FnDefParamType,
    IfExpr(IfExprLink),
    Impl(ImplLink),
    LoopBlock,
    ModuleItem,
    Op(OpLink),
    Path(PathLink),
    Range(RangeLink),
    Root,
    SliceLiteral(SliceLiteralLink),
    StructDef(StructDefLink),
    StructTypeFieldType,
    StructLiteral(StructLiteralLink),
    TypeAlias(TypeAliasLink),
    TyExpr(TyExprLink),
    UsePath,
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
    Def,
    TypeParam,
    Param,
    RetType,
    Body,
}

#[derive(Clone, Copy, Debug)]
pub enum FnCallLink {
    Callee,
    Arg,
}

#[derive(Clone, Copy, Debug)]
pub enum IfExprLink {
    Cond,
    IfTrue,
    IfFalse,
}

#[derive(Clone, Copy, Debug)]
pub enum ImplLink {
    Trait,
    For,
    TypeParam,
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
pub enum StructDefLink {
    Type,
    TypeParam,
}

#[derive(Clone, Copy, Debug)]
pub enum SliceLiteralLink {
    Item,
    Len,
}

#[derive(Clone, Copy, Debug)]
pub enum TyExprLink {
    Ref,
    Path,
    Struct,
    Slice(SliceTypeLink),
}

#[derive(Clone, Copy, Debug)]
pub enum SliceTypeLink {
    Item,
    Len,
}

#[derive(Clone, Copy, Debug)]
pub enum LetLink {
    Def,
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
    SegmentItemTyParams,
    EndIdentTyParams,
}

#[derive(Clone, Copy, Debug)]
pub enum StructLiteralLink {
    Name,
    Field,
    FieldValue,
}

#[derive(Clone, Copy, Debug)]
pub enum TypeAliasLink {
    TyParam,
    Ty,
}

#[derive(Clone, Copy)]
pub struct HirVisitorCtx {
    pub node: NodeId,
    pub kind: NodeKind,
    pub link: NodeLink,
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
        self.visitor.before_node(HirVisitorCtx { node, kind, link: link_kind });
    }

    fn after_node(&mut self, node: NodeId, kind: NodeKind, link_kind: NodeLink) {
        self.visitor.after_node(HirVisitorCtx { node, kind, link: link_kind });
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
                let FnCall { callee, args: params, .. } = self.hir.fn_call(node);
                self.traverse0(*callee, NodeLink::FnCall(FnCallLink::Callee));
                for param in params {
                    self.traverse0(param.value, NodeLink::FnCall(FnCallLink::Arg));
                }
            },
            NodeKind::FnDef => {
                let FnDef {
                    ty_params,
                    params,
                    ret_ty,
                    body,
                    ..
                } = self.hir.fn_def(node);

                for &ty_param in ty_params {
                    self.traverse0(ty_param, NodeLink::Fn(FnLink::TypeParam));
                }
                for &param in params {
                    self.traverse0(param, NodeLink::Fn(FnLink::Param));
                }
                if let &Some(ret_ty) = ret_ty {
                    self.traverse0(ret_ty, NodeLink::Fn(FnLink::RetType));
                }
                if let &Some(body) = body {
                    self.traverse0(body, NodeLink::Fn(FnLink::Body));
                }
            },
            NodeKind::FnDefParam => {
                let &FnDefParam { ty, .. } = self.hir.fn_def_param(node);
                self.traverse0(ty, NodeLink::FnDefParamType);
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
                let Impl { ty_params, trait_, for_, items } = self.hir.impl_(node);
                for &ty_param in ty_params {
                    self.traverse0(ty_param, NodeLink::Impl(ImplLink::TypeParam));
                }
                if let &Some(trait_) = trait_ {
                    self.traverse0(trait_, NodeLink::Impl(ImplLink::Trait));
                }
                self.traverse0(*for_, NodeLink::Impl(ImplLink::For));
                for &item in items {
                    self.traverse0(item, NodeLink::Impl(ImplLink::Item));
                }
            },
            NodeKind::Let => {
                let &Let { def } = self.hir.let_(node);
                self.traverse0(def, NodeLink::Let(LetLink::Def));
            }
            NodeKind::LetDef => {
                let &LetDef { ty, init, .. } = self.hir.let_def(node);
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
                if let Some(ty_args) = ty_args {
                    for &node in &ty_args.value {
                        self.traverse0(node, NodeLink::Path(PathLink::EndIdentTyParams));
                    }
                }
            },
            NodeKind::PathEndStar => {},
            NodeKind::PathSegment => {
                let PathSegment { prefix, suffix } = self.hir.path_segment(node);
                for PathItem { ident: _, ty_args } in prefix {
                    if let Some(ty_args) = ty_args {
                        for &node in &ty_args.value {
                            self.traverse0(node, NodeLink::Path(PathLink::SegmentItemTyParams));
                        }
                    }
                }
                for &node in suffix {
                    self.traverse0(node, NodeLink::Path(PathLink::SegmentSuffix));
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
            NodeKind::SliceLiteral => {
                let SliceLiteral { items, len } = self.hir.slice_literal(node);
                for &item in items {
                    self.traverse0(item, NodeLink::SliceLiteral(SliceLiteralLink::Item));
                }
                if let &Some(len) = len {
                    self.traverse0(len, NodeLink::SliceLiteral(SliceLiteralLink::Len));
                }
            },
            NodeKind::Struct => {
                let Struct { ty_params, ty, .. } = self.hir.struct_(node);
                for &ty_param in ty_params {
                    self.traverse0(ty_param, NodeLink::StructDef(StructDefLink::TypeParam));
                }
                self.traverse0(*ty, NodeLink::StructDef(StructDefLink::Type));
            },
            NodeKind::StructType => {
                let StructType { fields, .. } = self.hir.struct_type(node);
                for &StructTypeField { ty, .. } in fields {
                    self.traverse0(ty, NodeLink::StructTypeFieldType);
                }
            },
            NodeKind::StructLiteral => {
                let StructLiteral { name, fields, .. } = self.hir.struct_literal(node);
                if let Some(name) = *name {
                    self.traverse0(name, NodeLink::StructLiteral(StructLiteralLink::Name));
                }
                for &field in fields {
                    self.traverse0(field, NodeLink::StructLiteral(StructLiteralLink::Field));
                }
            },
            NodeKind::StructLiteralField => {
                let value = self.hir.struct_literal_field(node).value;
                self.traverse0(value, NodeLink::StructLiteral(StructLiteralLink::FieldValue))
            }
            NodeKind::TyExpr => {
                let TyExpr { data, .. } = self.hir.ty_expr(node);
                match &data.value {
                    &TyData::Path(n) => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Path)),
                    &TyData::Ref(n) => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Ref)),
                    &TyData::Slice(SliceType { item_ty, len }) => {
                        self.traverse0(item_ty, NodeLink::TyExpr(TyExprLink::Slice(SliceTypeLink::Item)));
                        if let Some(len) = len {
                            self.traverse0(len, NodeLink::TyExpr(TyExprLink::Slice(SliceTypeLink::Len)));
                        }
                    },
                    &TyData::Struct(n)  => self.traverse0(n, NodeLink::TyExpr(TyExprLink::Struct)),
                }
            },
            NodeKind::TypeAlias => {
                let TypeAlias { vis: _, name: _, ty_params, ty } = self.hir.type_alias(node);
                for &ty_param in ty_params {
                    self.traverse0(ty_param, NodeLink::TypeAlias(TypeAliasLink::TyParam));
                }
                self.traverse0(*ty, NodeLink::TypeAlias(TypeAliasLink::Ty));
            },
            NodeKind::TypeParam => {},
            NodeKind::Use => {
                let Use { path , ..} = self.hir.use_(node);
                self.traverse0(*path, NodeLink::UsePath);
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