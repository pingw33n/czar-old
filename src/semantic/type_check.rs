use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use enum_map_derive::Enum;
use if_chain::if_chain;
use slab::Slab;
use std::cell::RefCell;
use std::collections::HashSet;

use crate::hir::*;
use crate::hir::traverse::*;
use crate::package::{GlobalNodeId, PackageId, Packages};

use super::*;
use resolve::{ResolveData, Resolver};
use discover::{DiscoverData, NsKind};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberType {
    Float,
    Int,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sign {
    Signed,
    Unsigned,
}

#[derive(Clone, Copy, Debug, Enum, Eq, PartialEq)]
pub enum PrimitiveType {
    Bool,
    F32,
    F64,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    I128,
    U128,
    ISize,
    USize,
    Unit,
}

impl PrimitiveType {
    pub fn as_number(self) -> Option<NumberType> {
        use PrimitiveType::*;
        match self {
            | I8
            | U8
            | I16
            | U16
            | I32
            | U32
            | I64
            | U64
            | I128
            | U128
            | ISize
            | USize
            => Some(NumberType::Int),

            | F32
            | F64
            => Some(NumberType::Float),

            | Bool
            | Unit
            => None,
        }
    }

    pub fn int_sign(self) -> Option<Sign> {
        use PrimitiveType::*;
        match self {
            | I8
            | I16
            | I32
            | I64
            | I128
            | ISize
            => Some(Sign::Signed),

            | U8
            | U16
            | U32
            | U64
            | U128
            | USize
            => Some(Sign::Signed),

            | Bool
            | F32
            | F64
            | Unit
            => None,
        }
    }
}

#[derive(Debug)]
pub struct Type {
    package_id: PackageId,
    id: LocalTypeId,
    node: NodeId,
    data: Option<TypeData>,
}

impl Type {
    pub fn id(&self) -> TypeId {
        (self.package_id, self.id)
    }

    pub fn node(&self) -> GlobalNodeId {
        (self.package_id, self.node)
    }

    pub fn data(&self) -> &TypeData {
        self.data.as_ref().unwrap()
    }
}

#[derive(Debug, EnumAsInner)]
pub enum TypeData {
    Fn(FnType),
    Primitive(PrimitiveType),
    Struct(StructType),
    Type(TypeId),
    UnknownNumber(NumberType)
}

impl TypeData {
    pub fn as_number(&self) -> Option<NumberType> {
        use TypeData::*;
        match self {
            Primitive(v) => v.as_number(),
            UnknownNumber(v) => Some(*v),
            _ => None,
        }
    }
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

pub type LocalTypeId = usize;

pub type TypeId = (PackageId, LocalTypeId);

#[derive(Default)]
pub struct Types {
    types: Slab<Type>,
    typings: NodeMap<TypeId>,
    primitive_types: Option<Box<EnumMap<PrimitiveType, Option<LocalTypeId>>>>,
    path_to_target: NodeMap<GlobalNodeId>,
}

impl Types {
    pub fn type_(&self, id: LocalTypeId) -> &Type {
        &self.types[id]
    }

    pub fn type_mut(&mut self, id: LocalTypeId) -> &mut Type {
        &mut self.types[id]
    }

    pub fn insert_type(&mut self, node: GlobalNodeId, data: Option<TypeData>) -> TypeId {
        let e = self.types.vacant_entry();
        let id = e.key();
        e.insert(Type {
            package_id: node.0,
            id,
            node: node.1,
            data,
        });
        (node.0, id)
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

    pub fn primitive(&self, ty: PrimitiveType) -> LocalTypeId {
        self.primitive_types.as_ref().unwrap()[ty]
            .unwrap()
    }

    pub fn target_of(&self, path: NodeId) -> GlobalNodeId {
        self.path_to_target[&path]
    }

    fn insert_path_to_target(&mut self, path: NodeId, target: GlobalNodeId) {
        assert!(self.path_to_target.insert(path, target).is_none());
    }
}

pub struct TypeCheck<'a> {
    pub package_id: PackageId,
    pub hir: &'a Hir,
    pub discover_data: &'a DiscoverData,
    pub resolve_data: &'a ResolveData,
    pub packages: &'a Packages,
}

impl TypeCheck<'_> {
    pub fn run(self) -> Types {
        let mut types = Types::default();
        let tc = &mut Impl {
            resolve_data: self.resolve_data,
            types: &mut types,
            unknown_num_types: Default::default(),
            package_id: self.package_id,
            packages: self.packages,
            reso_ctxs: Default::default(),
            #[cfg(debug_assertions)]
            type_id_set: Default::default(),
        };
        if self.package_id.is_std() {
            tc.build_primitive_types(self.discover_data, self.hir);
        }
        self.hir.traverse(tc);
        if let Some(entry_point) = self.resolve_data.entry_point() {
            match tc.unaliased_typing(entry_point).data() {
                TypeData::Fn(FnType { args, result, unsafe_, extern_ }) => {
                    if args.len() != 0 {
                        fatal(self.hir.node_kind(entry_point).span, "`main` function must not accept arguments");
                    }
                    if !matches!(tc.unalias_type(*result).data(), TypeData::Primitive(PrimitiveType::Unit)) {
                        fatal(self.hir.node_kind(entry_point).span, "`main` function must have unit return type");
                    }
                    if *unsafe_ {
                        fatal(self.hir.node_kind(entry_point).span, "`main` function must not be unsafe");
                    }
                    if *extern_ {
                        fatal(self.hir.node_kind(entry_point).span, "`main` function must not be external");
                    }
                }
                _ => {
                    let node_kind = self.hir.node_kind(entry_point);
                    fatal(node_kind.span, format_args!("expected `main` function, but found {:?}",
                        node_kind.value));
                }
            }
        }
        for (_, ty) in &types.types {
            assert!(ty.data.is_some(), "{:?} {:?}", ty, self.hir.node_kind(ty.node));
        }
        types
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResoCtx {
    Import,
    Type,
    Value,
}

struct Impl<'a> {
    resolve_data: &'a ResolveData,
    types: &'a mut Types,
    unknown_num_types: HashSet<LocalTypeId>,
    package_id: PackageId,
    packages: &'a Packages,
    reso_ctxs: Vec<ResoCtx>,
    #[cfg(debug_assertions)]
    type_id_set: RefCell<HashSet<TypeId>>,
}

impl Impl<'_> {
    pub fn build_primitive_types(&mut self, discover_data: &DiscoverData, hir: &Hir) {
        let resolver = Resolver {
            discover_data,
            resolve_data: &Default::default(),
            hir,
            package_id: PackageId::std(),
            packages: &Packages::default(),
        };
        self.types.primitive_types = Some(Box::new(EnumMap::from(|ty| {
            use PrimitiveType::*;
            let path = match ty {
                Bool => &["bool", "bool"][..],
                F32 => &["f32", "f32"][..],
                F64 => &["f64", "f64"][..],
                I8 => &["i8", "i8"][..],
                U8 => &["u8", "u8"][..],
                I16 => &["i16", "i16"][..],
                U16 => &["u16", "u16"][..],
                I32 => &["i32", "i32"][..],
                U32 => &["u32", "u32"][..],
                I64 => &["i64", "i64"][..],
                U64 => &["u64", "u64"][..],
                I128 => &["i128", "i128"][..],
                U128 => &["u128", "u128"][..],
                ISize => &["isize", "isize"][..],
                USize => &["usize", "usize"][..],
                Unit => &["Unit"][..],
            };
            let node = resolver.resolve_in_package(path)
                .node(NsKind::Type)
                .unwrap();
            assert!(node.0.is_std());
            let ty = self.insert_typing(node.1, TypeData::Primitive(ty));
            Some(ty.1)
        })));
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
            &self.packages[package_id].types
        }
    }

    fn type_(&self, id: TypeId) -> &Type {
        self.types(id.0).type_(id.1)
    }

    fn unalias_type(&self, mut id: TypeId) -> &Type {
        #[cfg(debug_assertions)] {
            assert!(self.type_id_set.borrow_mut().is_empty());
        }
        let ty = loop {
            let ty = self.type_(id);
            if let Some(&next_id) = ty.data().as_type() {
                #[cfg(debug_assertions)] {
                    assert!(self.type_id_set.borrow_mut().insert(next_id));
                }
                id = next_id;
            } else {
                break ty;
            }
        };
        #[cfg(debug_assertions)] {
            self.type_id_set.borrow_mut().clear();
        }
        ty
    }

    fn insert_type(&mut self, node: NodeId, data: TypeData) -> TypeId {
        let unknown_number = data.as_unknown_number().is_some();
        let ty = self.types.insert_type((self.package_id, node), Some(data));
        if unknown_number {
            assert!(self.unknown_num_types.insert(ty.1));
        }
        ty
    }

    fn insert_typing(&mut self, node: NodeId, data: TypeData) -> TypeId {
        let ty = self.insert_type(node, data);
        self.types.insert_typing(node, ty);
        ty
    }

    fn primitive_type(&self, ty: PrimitiveType) -> TypeId {
        (PackageId::std(), self.types(PackageId::std()).primitive(ty))
    }

    fn unaliased_typing(&self, node: NodeId) -> &Type {
        self.try_unaliased_typing(node).unwrap()
    }

    fn try_unaliased_typing(&self, node: NodeId) -> Option<&Type> {
        let ty = self.types.try_typing(node)?;
        Some(self.unalias_type(ty))
    }

    fn begin_typing(&mut self, node: NodeId) -> TypeId {
        let ty = self.types.insert_type((self.package_id, node), None);
        self.types.insert_typing(node, ty);
        ty
    }

    fn finish_typing(&mut self, node: NodeId, ty: TypeId) {
        if let Some(id) = self.types.try_typing(node) {
            assert_eq!(id.0, self.package_id);
            let typ = self.types.type_mut(id.1);
            assert_eq!(typ.node(), (self.package_id, node));
            assert!(typ.data.replace(TypeData::Type(ty)).is_none());
        } else {
            self.types.insert_typing(node, ty)
        }
    }

    fn hir<'a>(&'a self, this_hir: &'a Hir, package_id: PackageId) -> &'a Hir {
        if package_id == self.package_id {
            this_hir
        } else {
            &self.packages[package_id].hir
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
                    .unwrap_or_else(|| self.primitive_type(PrimitiveType::Unit));
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
            | NodeKind::Use
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
                    .map(|n| self.unaliased_typing(n).id())
                    .unwrap_or(self.primitive_type(PrimitiveType::Unit));
                if let Some(body) = *body {
                    self.unify(self.types.typing(body), formal_ret_ty);

                    let actual_ret_ty = self.unaliased_typing(body);
                    if actual_ret_ty.id() != formal_ret_ty {
                        let span = ctx.hir.node_kind(ctx.node).span;
                        fatal(span, format_args!("`fn` actual type {:?} is incompatible with formal return type {:?}",
                            actual_ret_ty, self.unalias_type(formal_ret_ty)));
                    }
                    self.handle_unknown_num_types();
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
                        | FnDecl
                        | Module
                        | Struct
                        | Use
                        | While
                        => self.primitive_type(PrimitiveType::Unit),
                        _ => self.types.typing(expr)
                    }
                } else {
                    self.primitive_type(PrimitiveType::Unit)
                }
            }
            NodeKind::FnCall => {
                let FnCall {
                    callee,
                    kind,
                    args: actual_args,
                    .. } = ctx.hir.fn_call(ctx.node);
                let (callee_node, res) = {
                    let callee_ty = self.unaliased_typing(*callee);
                    if *kind != FnCallKind::Free {
                        unimplemented!();
                    }
                    let res = if let Some(v) = callee_ty.data().as_fn() {
                        v.result
                    } else {
                        let span = ctx.hir.node_kind(*callee).span;
                        fatal(span, "expected function");
                    };
                    let callee_node = callee_ty.node();
                    (callee_node, res)
                };

                let formal_args = self.hir(ctx.hir, callee_node.0).fn_decl(callee_node.1).args.clone();

                if actual_args.len() != formal_args.len() {
                    let name = &self.hir(ctx.hir, callee_node.0).fn_decl(callee_node.1).name.value;
                    fatal(ctx.hir.node_kind(ctx.node).span, format!(
                        "`fn`: `{}`: invalid number of actual parameters: expected {}, found {}",
                        name,
                        formal_args.len(), actual_args.len()));
                }

                for (actual, &formal) in actual_args
                    .iter()
                    .zip(formal_args.iter())
                {
                    self.unify(self.types.typing(actual.value), self.types(callee_node.0).typing(formal));

                    let formal_ty = self.unalias_type(self.types(callee_node.0).typing(formal));
                    let actual_ty = self.unaliased_typing(actual.value);
                    if actual_ty.id() != formal_ty.id() {
                        fatal(ctx.hir.node_kind(actual.value).span, format!(
                            "`fn`: incompatible actual `{:?}` and formal `{:?}` arg types",
                            actual_ty, formal_ty));
                    }
                }

                res
            }
            NodeKind::FnDecl => {
                unreachable!()
            }
            NodeKind::FnDeclArg => {
                self.types.typing(ctx.hir.fn_decl_arg(ctx.node).ty)
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = ctx.hir.if_expr(ctx.node);
                if !matches!(self.unaliased_typing(cond).data(), TypeData::Primitive(PrimitiveType::Bool)) {
                    let span = ctx.hir.node_kind(cond).span;
                    fatal(span, "expected bool expr");
                }
                let if_true_ty = self.types.typing(if_true);
                if let Some(if_false) = if_false {
                    if self.types.typing(if_false) != if_true_ty {
                        let span = ctx.hir.node_kind(cond).span;
                        fatal(span, "`if` arms have incompatible types");
                    }
                }
                if_true_ty
            }
            NodeKind::Let => {
                self.primitive_type(PrimitiveType::Bool)
            }
            NodeKind::LetDecl => {
                let &LetDecl { ty, init, .. } = ctx.hir.let_decl(ctx.node);
                if let Some(ty) = ty {
                    if let Some(init) = init {
                        self.unify(self.types.typing(ty), self.types.typing(init));
                    }

                    let typ = self.types.typing(ty);
                    if let Some(init) = init {
                        if self.unaliased_typing(init).id() != self.unalias_type(typ).id() {
                            fatal(ctx.hir.node_kind(ty).span, "formal and actual variable types differ");
                        }
                    }
                    typ
                } else if let Some(init) = init {
                    self.types.typing(init)
                } else {
                    fatal(ctx.hir.node_kind(ctx.node).span, "can't infer variable type");
                }
            }
            NodeKind::Literal => {
                match ctx.hir.literal(ctx.node) {
                    &Literal::Bool(_) => self.primitive_type(PrimitiveType::Bool),
                    &Literal::Int(IntLiteral { ty, .. }) => {
                        if let Some(ty) = ty {
                            use IntTypeSuffix::*;
                            self.primitive_type(match ty {
                                I8 => PrimitiveType::I8,
                                U8 => PrimitiveType::U8,
                                I16 => PrimitiveType::I16,
                                U16 => PrimitiveType::U16,
                                I32 => PrimitiveType::I32,
                                U32 => PrimitiveType::U32,
                                I64 => PrimitiveType::I64,
                                U64 => PrimitiveType::U64,
                                I128 => PrimitiveType::I128,
                                U128 => PrimitiveType::U128,
                                ISize => PrimitiveType::ISize,
                                USize => PrimitiveType::USize,
                            })
                        } else {
                            self.insert_type(ctx.node, TypeData::UnknownNumber(NumberType::Int))
                        }
                    },
                    &Literal::Float(FloatLiteral { ty, .. }) => {
                        if let Some(ty) = ty {
                            use FloatTypeSuffix::*;
                            self.primitive_type(match ty {
                                F32 => PrimitiveType::F32,
                                F64 => PrimitiveType::F64,
                            })
                        } else {
                            self.insert_type(ctx.node, TypeData::UnknownNumber(NumberType::Float))
                        }
                    }
                    &Literal::Unit => self.primitive_type(PrimitiveType::Unit),
                    _ => unimplemented!()
                }
            }
            NodeKind::Module => return,
            NodeKind::Op => {
                match ctx.hir.op(ctx.node) {
                    &Op::Binary(op) => {
                        self.type_binary_op(op, ctx)
                    }
                    &Op::Unary(op) => {
                        self.type_unary_op(op, ctx)
                    }
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
                self.primitive_type(PrimitiveType::Unit)
            }
            NodeKind::Path => {
                if self.reso_ctx() == ResoCtx::Import {
                    return
                } else {
                    let segment = ctx.hir.path(ctx.node).segment;
                    let target = self.types.target_of(segment);
                    self.types.insert_path_to_target(ctx.node, target);
                    self.types.typing(segment)
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
                    if let Some(node) = reso.node(expected_ns_kind.unwrap_or(reso.type_or_other_kind().unwrap()));
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
                self.types.insert_path_to_target(ctx.node, (pkg, node));
                if pkg == self.package_id {
                    self.build_type(node, ctx.hir)
                } else {
                    self.packages[pkg].types.typing(node)
                }
            }
            NodeKind::PathSegment => {
                if_chain! {
                    if self.reso_ctx() != ResoCtx::Import;
                    if let Some(&suffix) = ctx.hir.path_segment(ctx.node).suffix.first();
                    then {
                        let target = self.types.target_of(suffix);
                        self.types.insert_path_to_target(ctx.node, target);
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
            | NodeKind::Use
            => {
                self.primitive_type(PrimitiveType::Unit)
            },
            _ => unimplemented!("{:?}", ctx.hir.node_kind(ctx.node))
        };
        self.finish_typing(ctx.node, ty);
    }

    fn type_binary_op(&mut self, BinaryOp { kind, left, right }: BinaryOp, ctx: HirVisitorCtx) -> TypeId {
        self.unify(self.types.typing(left), self.types.typing(right));

        let left_ty = self.unaliased_typing(left);
        let right_ty = self.unaliased_typing(right);
        use BinaryOpKind::*;
        match kind.value {
            | Eq
            | Gt
            | GtEq
            | Lt
            | LtEq
            | NotEq
            => {
                let ok = match (left_ty.data(), right_ty.data()) {
                    (TypeData::Primitive(l), TypeData::Primitive(r)) if l == r => true,
                    (TypeData::UnknownNumber(l), TypeData::UnknownNumber(r)) if l == r => true,
                    _ => false,
                };
                if !ok {
                    let op_span = ctx.hir.node_kind(ctx.node).span;
                    fatal(op_span, format_args!("operation `{}` at is not defined for {:?} and {:?}",
                        kind.value, left_ty, right_ty));
                }
                self.primitive_type(PrimitiveType::Bool)
            },
            Add | Div | Mul | Sub | Rem => {
                let ok = match (left_ty.data(), right_ty.data()) {
                    (TypeData::Primitive(l), TypeData::Primitive(r)) =>
                        l.as_number().is_some() && l == r,
                    (TypeData::UnknownNumber(l), TypeData::UnknownNumber(r)) => l == r,
                    _ => false,
                };
                if !ok {
                    let op_span = ctx.hir.node_kind(ctx.node).span;
                    fatal(op_span, format_args!("operation `{}` is not defined for {:?} and {:?}",
                        kind.value, left_ty, right_ty));
                }
                left_ty.id()
            }
            _ => unimplemented!(),
        }
    }

    fn type_unary_op(&mut self, UnaryOp { kind, arg }: UnaryOp, ctx: HirVisitorCtx) -> TypeId {
        let arg_ty = self.unaliased_typing(arg);
        use UnaryOpKind::*;
        match kind.value {
            Neg => {
                let ok = match arg_ty.data() {
                    TypeData::Primitive(prim) if prim.as_number().is_some() => true,
                    TypeData::UnknownNumber(_) => true,
                    _ => false,
                };
                if !ok {
                    let op_span = ctx.hir.node_kind(ctx.node).span;
                    fatal(op_span, format_args!("unary operation `{}` is not defined for {:?}",
                        kind.value, arg_ty));
                }
                arg_ty.id()
            }
            _ => todo!(),
        }
    }

    fn unify(&mut self, ty1: TypeId, ty2: TypeId) {
        if ty1 == ty2 {
            return;
        }
        let (ty, to_type) = {
            let ty1 = self.unalias_type(ty1);
            if ty1.id() == ty2 {
                return;
            }
            let ty2 = self.unalias_type(ty2);
            if ty1.id() == ty2.id() {
                return;
            }
            use TypeData::*;
            match (ty1.data(), ty2.data()) {
                (&UnknownNumber(num), Primitive(pt)) if pt.as_number() == Some(num) => (ty1.id(), ty2.id()),
                (Primitive(pt), &UnknownNumber(num)) if pt.as_number() == Some(num) => (ty2.id(), ty1.id()),
                (UnknownNumber(l), UnknownNumber(r)) if l == r => (ty1.id(), ty2.id()),
                _ => return,
            }
        };
        assert_eq!(ty.0, self.package_id);
        let typ = self.types.type_mut(ty.1);
        assert!(typ.data().as_unknown_number().is_some());
        assert!(self.unknown_num_types.remove(&ty.1));
        typ.data = Some(TypeData::Type(to_type));
    }

    fn handle_unknown_num_types(&mut self) {
        if self.unknown_num_types.is_empty() {
            return;
        }
        let i32 = self.primitive_type(PrimitiveType::I32);
        let f64 = self.primitive_type(PrimitiveType::F64);
        for ty in self.unknown_num_types.drain() {
            let fallback = match self.types.type_(ty).data().as_unknown_number().unwrap() {
                NumberType::Int => i32,
                NumberType::Float => f64,
            };
            let typ = self.types.type_mut(ty);
            typ.data = Some(TypeData::Type(fallback));
        }
    }

    fn has_complete_typing(&self, node: NodeId) -> bool {
        let id = if let Some(v) = self.types.try_typing(node) {
            v
        } else {
            return false;
        };
        if id.0 == self.package_id {
            self.types.type_(id.1).data.is_some()
        } else {
            debug_assert!(self.type_(id).data.is_some());
            true
        }
    }
}

impl HirVisitor for Impl<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        if let Some(v) = reso_ctx(ctx.link) {
            self.reso_ctxs.push(v);
        }
        if self.types.try_typing(ctx.node).is_none() {
            self.do_pre_typing(ctx);
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        self.check(ctx);

        if !self.has_complete_typing(ctx.node) {
            self.do_typing(ctx);
        }

        if let Some(v) = reso_ctx(ctx.link) {
            assert_eq!(self.reso_ctxs.pop().unwrap(), v);
        }
    }
}

fn reso_ctx(link: NodeLink) -> Option<ResoCtx> {
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

        UsePath => ResoCtx::Import,

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