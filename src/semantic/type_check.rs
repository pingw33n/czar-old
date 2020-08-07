use enum_as_inner::EnumAsInner;
use if_chain::if_chain;
use slab::Slab;
use std::collections::HashMap;

use crate::hir::*;
use crate::hir::traverse::*;

use super::*;
use super::discover::{DiscoverData, NsKind};
use crate::package::{GlobalNodeId, PackageId, Packages};
use super::resolve::ResolveData;
use crate::semantic::resolve::Resolver;

#[derive(Clone, Copy, Debug)]
pub enum PrimitiveType {
    Bool,
    I32,
    Unit,
}

#[derive(Debug)]
pub struct Type {
    pub node: GlobalNodeId,
    pub data: Option<TypeData>,
}

impl Type {
    pub fn data(&self) -> &TypeData {
        self.data.as_ref().unwrap()
    }
}

#[derive(Debug, EnumAsInner)]
pub enum TypeData {
    Fn(FnType),
    Primitive(PrimitiveType),
    Struct(StructType),
    Type(LocalTypeId),
}

#[derive(Debug)]
pub struct FnType {
    pub args: Vec<TypeId>,
    pub result: TypeId,
    pub unsafe_: bool,
    pub extern_: bool,
}

#[derive(Debug)]
pub struct StructType {
    pub fields: Vec<TypeId>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LangType {
    Bool,
    I32,
    Unit,
}

pub type LocalTypeId = usize;

pub type TypeId = (PackageId, LocalTypeId);

#[derive(Default)]
pub struct Types {
    types: Slab<Type>,
    typings: NodeMap<TypeId>,
    lang_types: HashMap<LangType, LocalTypeId>,
}

impl Types {
    pub fn type_(&self, id: LocalTypeId) -> &Type {
        &self.types[id]
    }

    pub fn type_mut(&mut self, id: LocalTypeId) -> &mut Type {
        &mut self.types[id]
    }

    pub fn insert_type(&mut self, ty: Type) -> LocalTypeId {
        self.types.insert(ty)
    }

    pub fn typing(&self, node: NodeId) -> TypeId {
        self.typings[&node]
    }

    pub fn try_typing(&self, node: NodeId) -> Option<TypeId> {
        self.typings.get(&node).copied()
    }

    pub fn insert_typing(&mut self, node: NodeId, ty: TypeId) {
        assert!(self.typings.insert(node, ty).is_none());
    }

    pub fn lang(&self, ty: LangType) -> LocalTypeId {
        self.lang_types[&ty]
    }

    pub fn set_lang(&mut self, lang: LangType, ty: LocalTypeId) {
        assert!(self.lang_types.insert(lang, ty).is_none());
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResoCtx {
    Import,
    Type,
    Value,
}

pub struct TypeCheck<'a> {
    pub resolve_data: &'a ResolveData,
    pub types: &'a mut Types,
    pub package_id: PackageId,
    pub packages: &'a Packages,
    pub reso_ctxs: Vec<ResoCtx>,
}

impl TypeCheck<'_> {
    pub fn build_lang_types(&mut self, discover_data: &DiscoverData, hir: &Hir) {
        let resolver = Resolver {
            discover_data,
            resolve_data: &Default::default(),
            hir,
            package_id: PackageId::std(),
            packages: &Packages::default(),
        };
        for &(path, lang, ty) in &[
            (&["Unit"][..], LangType::Unit, PrimitiveType::Unit),
            (&["bool", "bool"][..], LangType::Bool, PrimitiveType::Bool),
            (&["i32", "i32"][..], LangType::I32, PrimitiveType::I32),
        ] {
            let node = resolver.resolve_in_package(path)
                .nodes()[NsKind::Type]
                .unwrap();
            assert!(node.0.is_std());
            let ty = self.insert_typing(node.1, TypeData::Primitive(ty));
            self.types.set_lang(lang, ty.1);
        }
    }

    fn build_type(&mut self, node: NodeId, hir: &Hir) -> TypeId {
        if let Some(ty) = self.types.try_typing(node) {
            ty
        } else {
            hir.traverse_from(node, self);
            self.types.typing(node)
        }
    }

    fn types(&self, package_id: PackageId) -> &Types {
        if package_id == self.package_id {
            &self.types
        } else {
            &self.packages.get(package_id).types
        }
    }

    fn type_(&self, id: TypeId) -> &Type {
        self.types(id.0).type_(id.1)
    }

    fn direct_type(&self, id: TypeId) -> &Type {
        let ty = self.type_(id);
        if let Some(&next_id) = ty.data().as_type() {
            let ty = self.type_((id.0, next_id));
            assert!(ty.data().as_type().is_none());
            ty
        } else {
            ty
        }
    }

    fn insert_type(&mut self, node: NodeId, data: TypeData) -> TypeId {
        (self.package_id, self.types.insert_type(Type {
            node: (self.package_id, node),
            data: Some(data),
        }))
    }

    fn insert_typing(&mut self, node: NodeId, data: TypeData) -> TypeId {
        let ty = self.insert_type(node, data);
        self.types.insert_typing(node, ty);
        ty
    }

    fn lang_type(&self, ty: LangType) -> TypeId {
        (PackageId::std(), self.types(PackageId::std()).lang(ty))
    }

    fn typing(&self, node: NodeId) -> &Type {
        self.try_typing(node).unwrap()
    }

    fn try_typing(&self, node: NodeId) -> Option<&Type> {
        let (pkg, ty) = self.types.try_typing(node)?;
        Some(self.types(pkg).type_(ty))
    }

    pub fn begin_typing(&mut self, node: NodeId) -> TypeId {
        let ty = (self.package_id, self.types.insert_type(Type {
            node: (self.package_id, node),
            data: None
        }));
        self.types.insert_typing(node, ty);
        ty
    }

    pub fn finish_typing(&mut self, node: NodeId, ty: TypeId) {
        if let Some(id) = self.types.try_typing(node) {
            assert_eq!(id.0, self.package_id);
            let typ = self.types.type_mut(id.1);
            assert_eq!(typ.node, (self.package_id, node));
            assert_eq!(ty.0, self.package_id);
            assert!(typ.data.replace(TypeData::Type(ty.1)).is_none());
        } else {
            self.types.insert_typing(node, ty)
        }
    }

    fn hir<'a>(&'a self, this_hir: &'a Hir, package_id: PackageId) -> &'a Hir {
        if package_id == self.package_id {
            this_hir
        } else {
            &self.packages.get(package_id).hir
        }
    }


    fn reso_ctx(&self) -> ResoCtx {
        *self.reso_ctxs.last().unwrap()
    }

    fn do_pre_typing(&mut self, ctx: HirVisitorCtx) {
        match ctx.kind {
            NodeKind::FnDecl => {
                let FnDecl {
                    args,
                    ret_ty,
                    unsafe_,
                    body,
                    .. } = ctx.hir.fn_decl(ctx.node);
                let args: Vec<_> = args.iter()
                    .copied()
                    .map(|n| self.build_type(n, ctx.hir))
                    .collect();
                let result = ret_ty.map(|n| self.build_type(n, ctx.hir))
                    .unwrap_or_else(|| self.lang_type(LangType::Unit));
                self.insert_typing(ctx.node, TypeData::Fn(FnType {
                    args,
                    result,
                    unsafe_: unsafe_.is_some(),
                    extern_: body.is_none(),
                }));
            }
            NodeKind::Struct => {
                self.begin_typing(ctx.node);
            }
            | NodeKind::Block
            | NodeKind::FnCall
            | NodeKind::FnDeclArg
            | NodeKind::Fn_
            | NodeKind::IfExpr
            | NodeKind::Let
            | NodeKind::LetDecl
            | NodeKind::Literal
            | NodeKind::Module
            | NodeKind::Op
            | NodeKind::Path
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndIdent
            | NodeKind::PathEndStar
            | NodeKind::PathSegment
            | NodeKind::StructType
            | NodeKind::StructValue
            | NodeKind::TyExpr
            | NodeKind::UseStmt
            => {},
            _ => {
                unimplemented!("{:?}", ctx.hir.node_kind(ctx.node));
            },
        }
    }

    fn check(&mut self, ctx: HirVisitorCtx) {
        match ctx.kind {
            NodeKind::FnDecl => {
                let FnDecl {
                    ret_ty,
                    body,
                    .. } = ctx.hir.fn_decl(ctx.node);
                let formal_ret_ty = ret_ty
                    .map(|n| self.types.typing(n))
                    .unwrap_or(self.lang_type(LangType::Unit));
                if let Some(body) = *body {
                    let actual_ret_ty = self.types.typing(body);
                    if actual_ret_ty != formal_ret_ty {
                        let span = ctx.hir.node_kind(ctx.node).span;
                        fatal(span, format_args!("`fn` actual type {:?} is incompatible with formal return type {:?}",
                            self.direct_type(actual_ret_ty), self.direct_type(formal_ret_ty)));
                    }
                }
            },
            _ => {},
        }
    }

    fn do_typing(&mut self, ctx: HirVisitorCtx) {
        let ty = match ctx.kind {
            NodeKind::Block => {
                if let Some(&expr) = ctx.hir.block(ctx.node).exprs.last() {
                    use NodeKind::*;
                    match ctx.hir.node_kind(expr).value {
                        | Impl
                        | Loop
                        | Fn_
                        | Module
                        | Struct
                        | UseStmt
                        | While
                        => self.lang_type(LangType::Unit),
                        _ => self.types.typing(expr)
                    }
                } else {
                    self.lang_type(LangType::Unit)
                }
            }
            NodeKind::Fn_ => {
                self.types.typing(ctx.hir.fn_(ctx.node).decl)
            }
            NodeKind::FnCall => {
                let FnCall {
                    callee,
                    kind,
                    args: actual_args,
                    .. } = ctx.hir.fn_call(ctx.node);
                let callee_ty = self.typing(*callee);
                if *kind != FnCallKind::Free {
                    unimplemented!();
                }
                let fn_ty = if let Some(v) = callee_ty.data().as_fn() {
                    v
                } else {
                    let span = ctx.hir.node_kind(*callee).span;
                    panic!("[{}:{}] expected function", span.start, span.end);
                };

                let formal_args = &self.hir(ctx.hir, callee_ty.node.0).fn_decl(callee_ty.node.1).args;
                assert_eq!(actual_args.len(), formal_args.len());
                for (actual, formal) in actual_args
                    .iter()
                    .zip(formal_args.iter())
                {
                    if self.types.typing(actual.value) != self.types.typing(*formal) {
                        dbg!(self.types.typing(actual.value), self.types.typing(*formal));
                        dbg!(ctx.hir.node_kind(actual.value), ctx.hir.node_kind(*formal));
                        fatal(ctx.hir.node_kind(actual.value).span, "`fn`: incompatible actual and formal arg types");
                    }
                }

                fn_ty.result
            }
            NodeKind::FnDecl => {
                unreachable!()
            }
            NodeKind::FnDeclArg => {
                self.types.typing(ctx.hir.fn_decl_arg(ctx.node).ty)
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = ctx.hir.if_expr(ctx.node);
                if !matches!(self.typing(cond).data(), TypeData::Primitive(PrimitiveType::Bool)) {
                    let span = ctx.hir.node_kind(cond).span;
                    panic!("[{}:{}] expected bool expr", span.start, span.end);
                }
                let if_true_ty = self.types.typing(if_true);
                if let Some(if_false) = if_false {
                    if self.types.typing(if_false) != if_true_ty {
                        let span = ctx.hir.node_kind(cond).span;
                        panic!("[{}:{}] `if` arms have incompatible types", span.start, span.end);
                    }
                }
                if_true_ty
            }
            NodeKind::Let => {
                self.lang_type(LangType::Bool)
            }
            NodeKind::LetDecl => {
                self.types.typing(ctx.hir.let_decl(ctx.node).ty.expect("unimplemented"))
            }
            NodeKind::Literal => {
                match ctx.hir.literal(ctx.node) {
                    &Literal::Bool(_) => self.lang_type(LangType::Bool),
                    &Literal::Int(IntLiteral { ty, .. }) => {
                        if let Some(ty) = ty {
                            match ty {
                                IntTypeSuffix::I32 => self.lang_type(LangType::I32),
                                _ => unimplemented!()
                            }
                        } else {
                            // FIXME
                            self.lang_type(LangType::I32)
                        }
                    },
                    &Literal::Unit => self.lang_type(LangType::Unit),
                    _ => unimplemented!()
                }
            }
            NodeKind::Module => return,
            NodeKind::Op => {
                match ctx.hir.op(ctx.node) {
                    &Op::Binary(BinaryOp { kind, left, right }) => {
                        let left_ty = self.types.typing(left);
                        let right_ty = self.types.typing(right);
                        match kind.value {
                            BinaryOpKind::LtEq => {
                                {
                                    let left_ty = &self.direct_type(left_ty);
                                    let right_ty = &self.direct_type(right_ty);
                                    if !matches!(left_ty.data(), TypeData::Primitive(PrimitiveType::I32)) ||
                                        !matches!(right_ty.data(), TypeData::Primitive(PrimitiveType::I32))
                                    {
                                        let op_span = ctx.hir.node_kind(ctx.node).span;
                                        fatal(op_span, format_args!("operation `<=` at is not defined for {:?} and {:?}",
                                            left_ty, right_ty));
                                    }
                                }
                                self.lang_type(LangType::Bool)
                            },
                            BinaryOpKind::Add => {
                                {
                                    let left_ty = &self.direct_type(left_ty);
                                    let right_ty = &self.direct_type(right_ty);
                                    if !matches!(left_ty.data(), TypeData::Primitive(PrimitiveType::I32)) ||
                                        !matches!(right_ty.data(), TypeData::Primitive(PrimitiveType::I32))
                                    {
                                        let op_span = ctx.hir.node_kind(ctx.node).span;
                                        panic!("operation `+` at [{}:{}] is not defined for {:?} and {:?}",
                                            op_span.start, op_span.end,
                                            left_ty, right_ty);
                                    }
                                }
                                left_ty
                            }
                            BinaryOpKind::Sub => {
                                {
                                    let left_ty = &self.direct_type(left_ty);
                                    let right_ty = &self.direct_type(right_ty);
                                    if !matches!(left_ty.data(), TypeData::Primitive(PrimitiveType::I32)) ||
                                        !matches!(right_ty.data(), TypeData::Primitive(PrimitiveType::I32))
                                    {
                                        let op_span = ctx.hir.node_kind(ctx.node).span;
                                        panic!("operation `-` at [{}:{}] is not defined for {:?} and {:?}",
                                            op_span.start, op_span.end,
                                            left_ty, right_ty);
                                    }
                                }
                                left_ty
                            }
                            _ => unimplemented!(),
                        }
                    }
                    _ => unimplemented!(),
                }
            }
            NodeKind::Struct => {
                self.types.typing(ctx.hir.struct_(ctx.node).ty)
            }
            NodeKind::StructType => {
                let fields = &ctx.hir.struct_type(ctx.node).fields;
                let fields: Vec<_> = fields
                    .iter()
                    .map(|f| self.types.typing(f.ty))
                    .collect();
                self.insert_type(ctx.node, TypeData::Struct(StructType {
                    fields,
                }))
            }
            NodeKind::StructValue => {
                let StructValue { name, anonymous_fields, fields } = ctx.hir.struct_value(ctx.node);
                assert!(anonymous_fields.is_none() || !fields.is_empty());
                if name.is_some() || !fields.is_empty() {
                    unimplemented!();
                }
                self.lang_type(LangType::Unit)
            }
            NodeKind::Path => {
                if self.reso_ctx() == ResoCtx::Import {
                    return
                } else {
                    self.types.typing(ctx.hir.path(ctx.node).segment)
                }
            }
            NodeKind::PathEndIdent => {
                let reso = self.resolve_data.resolution_of(ctx.node);
                assert!(!reso.is_empty());
                let reso_ctx = self.reso_ctx();
                let expected_ns_kind = match reso_ctx {
                    ResoCtx::Import => None,
                    ResoCtx::Type => Some(NsKind::Type),
                    ResoCtx::Value => Some(NsKind::Value),
                };
                let (pkg, node) = if_chain! {
                    if let Some(node) = reso.nodes()[expected_ns_kind.unwrap_or(reso.type_or_other_kind().unwrap())];
                    let kind = self.hir(ctx.hir, node.0).node_kind(node.1).value;
                    if is_valid_in_reso_ctx(kind, reso_ctx);
                    then {
                        node
                    } else {
                        let found = reso.type_or_other().unwrap();
                        let found_kind = self.hir(ctx.hir, found.0).node_kind(found.1).value;
                        if let Some(expected_ns_kind) = expected_ns_kind {
                            fatal(ctx.hir.node_kind(ctx.node).span,
                                format_args!("expected {:?}, found {:?}", expected_ns_kind, found_kind));
                        } else {
                            fatal(ctx.hir.node_kind(ctx.node).span,
                                format_args!("{:?} can't be imported", found_kind));
                        }
                    }
                };
                if reso_ctx == ResoCtx::Import {
                    return;
                }
                if pkg == self.package_id {
                    self.build_type(node, ctx.hir)
                } else {
                    self.packages.get(pkg).types.typing(node)
                }
            }
            NodeKind::PathSegment => {
                if_chain! {
                    if self.reso_ctx() != ResoCtx::Import;
                    if let Some(&suffix) = ctx.hir.path_segment(ctx.node).suffix.first();
                    then {
                        self.types.typing(suffix)
                    } else {
                        return;
                    }
                }
            }
            NodeKind::TyExpr => {
                let TyExpr { muta: _, data } = ctx.hir.ty_expr(ctx.node);
                match &data.value {
                    TyData::Array(_) => unimplemented!(),
                    TyData::Ptr(_) => unimplemented!(),
                    TyData::Ref(_) => unimplemented!(),
                    TyData::Slice(_) => unimplemented!(),
                    &TyData::Path(node) => {
                        self.types.typing(node)
                    }
                    TyData::Struct(_) => unimplemented!(),
                }
            }
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            | NodeKind::UseStmt
            => {
                self.lang_type(LangType::Unit)
            },
            _ => unimplemented!("{:?}", ctx.hir.node_kind(ctx.node))
        };
        self.finish_typing(ctx.node, ty);
    }
}

impl HirVisitor for TypeCheck<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        if let Some(v) = reso_req(ctx.link) {
            self.reso_ctxs.push(v);
        }
        if self.types.try_typing(ctx.node).is_none() {
            self.do_pre_typing(ctx);
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        self.check(ctx);

        if self.types.try_typing(ctx.node).is_none() {
            self.do_typing(ctx);
        }

        if let Some(v) = reso_req(ctx.link) {
            assert_eq!(self.reso_ctxs.pop().unwrap(), v);
        }
    }
}

fn reso_req(link: NodeLink) -> Option<ResoCtx> {
    use NodeLink::*;
    Some(match link {
        | BlockExpr
        | BlockFlowCtlValue
        | Cast(CastLink::Expr)
        | FieldAccessReceiver
        | FnCall(_)
        | Fn(FnLink::Body)
        | IfExpr(_)
        | Let(LetLink::Init)
        | LoopBlock
        | Op(_)
        | Range(_)
        | StructValueValue
        | TyExpr(TyExprLink::Array(ArrayLink::Len))
        | While(_)
        => ResoCtx::Value,

        | Cast(CastLink::Type)
        | Fn(FnLink::TypeArg)
        | Fn(FnLink::RetType)
        | FnDeclArgType
        | Impl(ImplLink::TypeArg)
        | Let(LetLink::Type)
        | Path(PathLink::EndIdentTyArgs)
        | Path(PathLink::SegmentItemTyArgs)
        | StructDecl(_)
        | StructTypeFieldType
        | TyExpr(_)
        => ResoCtx::Type,

        UseStmtPath => ResoCtx::Import,

        | Fn(_)
        | Impl(_)
        | Let(_)
        | ModuleItem
        | Path(_)
        | Root
        => return None,
    })
}

fn is_valid_in_reso_ctx(kind: NodeKind, reso_ctx: ResoCtx) -> bool {
    use NodeKind::*;
    match reso_ctx {
        ResoCtx::Import => {
            kind != LetDecl && (
                is_valid_in_reso_ctx(kind, ResoCtx::Type)
                || is_valid_in_reso_ctx(kind, ResoCtx::Value))
        },
        ResoCtx::Type => kind == Struct,
        ResoCtx::Value => {
            match kind {
                | FnDecl
                | FnDeclArg
                | LetDecl
                => true,
                _ => false,
            }
        },
    }
}