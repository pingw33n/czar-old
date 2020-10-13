use enum_as_inner::EnumAsInner;
use enum_map::EnumMap;
use enum_map_derive::Enum;
use if_chain::if_chain;
use slab::Slab;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::diag::{self, Diag, Severity};
use crate::hir::{self, *};
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
    Char,
    String,
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
            | Char
            | String
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
            | Char
            | F32
            | F64
            | String
            | Unit
            => None,
        }
    }
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use PrimitiveType::*;
        let s = match *self {
            Bool => "bool",
            F32 => "f32",
            F64 => "f64",
            I8 => "i8",
            U8 => "u8",
            I16 => "i16",
            U16 => "u16",
            I32 => "i32",
            U32 => "u32",
            I64 => "i64",
            U64 => "u64",
            I128 => "i128",
            U128 => "u128",
            ISize => "isize",
            USize => "usize",
            Unit => "{}",
            Char => "char",
            String => "String",
        };
        write!(f, "{}", s)
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
}

#[derive(Debug)]
pub struct StructType {
    pub fields: Vec<TypeId>,
}

pub type LocalTypeId = usize;

pub type TypeId = (PackageId, LocalTypeId);

#[derive(Default)]
pub struct CheckData {
    types: Slab<Type>,
    typings: NodeMap<TypeId>,
    primitive_types: Option<Box<EnumMap<PrimitiveType, LocalTypeId>>>,
    path_to_target: NodeMap<GlobalNodeId>,
    /// Maps `FieldAccess` and `StructValueField` nodes to the field index on a named struct.
    struct_fields: NodeMap<u32>,
    /// Unnamed structs introduced in this package.
    unnamed_structs: HashMap<UnnamedStructKey, LocalTypeId>,
}

impl CheckData {
    pub fn type_(&self, id: LocalTypeId) -> &Type {
        &self.types[id]
    }

    pub fn type_mut(&mut self, id: LocalTypeId) -> &mut Type {
        &mut self.types[id]
    }

    fn insert_type(&mut self, node: GlobalNodeId, data: Option<TypeData>) -> TypeId {
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

    fn insert_typing(&mut self, node: NodeId, ty: TypeId) {
        assert!(self.typings.insert(node, ty).is_none());
    }

    pub fn primitive(&self, ty: PrimitiveType) -> LocalTypeId {
        self.primitive_types.as_ref().unwrap()[ty]
    }

    pub fn target_of(&self, path: NodeId) -> GlobalNodeId {
        self.path_to_target[&path]
    }

    fn insert_path_to_target(&mut self, path: NodeId, target: GlobalNodeId) {
        assert!(self.path_to_target.insert(path, target).is_none());
    }

    pub fn struct_field(&self, node: NodeId) -> u32 {
        self.struct_fields[&node]
    }
}

#[derive(Debug)]
pub struct CheckError(());

pub type Result<T> = std::result::Result<T, CheckError>;

pub struct Check<'a> {
    pub package_id: PackageId,
    pub hir: &'a Hir,
    pub discover_data: &'a DiscoverData,
    pub resolve_data: &'a ResolveData,
    pub packages: &'a Packages,
    pub diag: Rc<RefCell<Diag>>,
}

impl<'a> Check<'a> {
    pub fn run(self) -> Result<CheckData> {
        let mut check_data = CheckData::default();

        let mut unnamed_structs = HashMap::new();
        for package in self.packages.iter() {
            for (k, ty) in &package.check_data.unnamed_structs {
                assert!(unnamed_structs.insert(k.clone(), (package.id, *ty)).is_none());
            }
        }

        let imp = &mut Impl {
            discover_data: self.discover_data,
            resolve_data: self.resolve_data,
            check_data: &mut check_data,
            unknown_num_types: Default::default(),
            package_id: self.package_id,
            packages: self.packages,
            reso_ctxs: Default::default(),
            #[cfg(debug_assertions)]
            type_id_set: Default::default(),
            unnamed_structs,
            hir: self.hir,
            diag: self.diag,
            errors: Default::default(),
        };
        if self.package_id.is_std() {
            imp.build_primitive_types();
        }
        self.hir.traverse(imp);
        if !imp.errors.borrow().fatal_in_mod {
            if let Some(entry_point) = self.resolve_data.entry_point() {
                match imp.unaliased_typing(entry_point).data() {
                    TypeData::Fn(FnType { args, result, unsafe_ }) => {
                        assert_eq!(args.len(), 0);
                        if !matches!(imp.unalias_type(*result).data(), TypeData::Primitive(PrimitiveType::Unit)) {
                            let node = self.hir.fn_decl(entry_point).ret_ty.unwrap();
                            imp.fatal(node, "`main` function must have unit return type".into());
                        }
                        if *unsafe_ {
                            let span = self.hir.fn_decl(entry_point).unsafe_.unwrap().span;
                            imp.fatal_span(entry_point, span, "`main` function must not be unsafe".into());
                        }
                        if self.hir.fn_decl(entry_point).body.is_none() {
                            imp.fatal(entry_point, "`main` function must not be external".into());
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
        let has_errors = imp.errors.borrow().has;
        for (_, ty) in &check_data.types {
            assert!(ty.data.is_some(), "{:?} {:?}", ty, self.hir.node_kind(ty.node));
        }
        if has_errors {
            Err(CheckError(()))
        } else {
            Ok(check_data)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResoCtx {
    Import,
    Type,
    Value,
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct UnnamedStructKey(Vec<(Option<Ident>, TypeId)>);

impl UnnamedStructKey {
    fn new(mut fields: Vec<(Option<Ident>, TypeId)>) -> Self {
        fields.sort_by(|a, b| a.0.cmp(&b.0));
        Self(fields)
    }

    fn field_types(&self) -> Vec<TypeId> {
        self.0.iter().map(|v| v.1).collect()
    }
}

#[derive(Default)]
struct Errors {
    /// Has any errors including non-fatal.
    has: bool,

    /// Has fatal module-level errors.
    /// When this is becomes `true`, no more checking is performed.
    fatal_in_mod: bool,

    /// Has fatal function-level errors.
    /// When a fatal error reported inside function body, no more checking of that function body is
    /// done.
    fatal_in_fn_decls: NodeMap<()>,
}

struct Impl<'a> {
    discover_data: &'a DiscoverData,
    resolve_data: &'a ResolveData,
    check_data: &'a mut CheckData,
    unknown_num_types: HashSet<LocalTypeId>,
    package_id: PackageId,
    packages: &'a Packages,
    reso_ctxs: Vec<ResoCtx>,
    #[cfg(debug_assertions)]
    type_id_set: RefCell<HashSet<TypeId>>,
    /// Unnamed structs across all packages.
    unnamed_structs: HashMap<UnnamedStructKey, TypeId>,
    hir: &'a Hir,
    diag: Rc<RefCell<Diag>>,
    errors: RefCell<Errors>,
}

impl Impl<'_> {
    pub fn build_primitive_types(&mut self) {
        assert!(self.package_id.is_std());
        let resolver = Resolver {
            discover_data: self.discover_data,
            resolve_data: &Default::default(),
            hir: self.hir,
            package_id: PackageId::std(),
            packages: &Packages::default(),
        };
        let map = Box::new(EnumMap::from(|ty| {
            use PrimitiveType::*;
            let path = match ty {
                Bool => &["bool", "bool"][..],
                Char => &["char", "char"][..],
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
                String => &["string", "String"][..],
                Unit => &["Unit"][..],
            };
            let (pkg, node) = resolver.resolve_in_package(path, None)
                .node(NsKind::Type)
                .unwrap();
            assert!(pkg.is_std());
            let (pkg, ty) = self.insert_typing(node, TypeData::Primitive(ty));
            assert!(pkg.is_std());
            ty
        }));
        assert!(self.check_data.primitive_types.replace(map).is_none());
    }

    fn build_type(&mut self, node: NodeId) -> TypeId {
        if let Some(ty) = self.check_data.try_typing(node) {
            ty
        } else {
            self.hir.traverse_from(node, self);
            self.check_data.typing(node)
        }
    }

    fn check_data(&self, package_id: PackageId) -> &CheckData {
        if package_id == self.package_id {
            &self.check_data
        } else {
            &self.packages[package_id].check_data
        }
    }

    fn type_(&self, id: TypeId) -> &Type {
        self.check_data(id.0).type_(id.1)
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
        let ty = self.check_data.insert_type((self.package_id, node), Some(data));
        if unknown_number {
            assert!(self.unknown_num_types.insert(ty.1));
        }
        ty
    }

    fn insert_typing(&mut self, node: NodeId, data: TypeData) -> TypeId {
        let ty = self.insert_type(node, data);
        self.check_data.insert_typing(node, ty);
        ty
    }

    fn primitive_type(&self, ty: PrimitiveType) -> TypeId {
        (PackageId::std(), self.check_data(PackageId::std()).primitive(ty))
    }

    fn unaliased_typing(&self, node: NodeId) -> &Type {
        self.try_unaliased_typing(node).unwrap()
    }

    fn try_unaliased_typing(&self, node: NodeId) -> Option<&Type> {
        let ty = self.check_data.try_typing(node)?;
        Some(self.unalias_type(ty))
    }

    fn begin_typing(&mut self, node: NodeId) -> TypeId {
        let ty = self.check_data.insert_type((self.package_id, node), None);
        self.check_data.insert_typing(node, ty);
        ty
    }

    fn finish_typing(&mut self, node: NodeId, ty: TypeId) {
        if let Some(id) = self.check_data.try_typing(node) {
            assert_eq!(id.0, self.package_id);
            let typ = self.check_data.type_mut(id.1);
            assert_eq!(typ.node(), (self.package_id, node));
            assert!(typ.data.replace(TypeData::Type(ty)).is_none());
        } else {
            self.check_data.insert_typing(node, ty)
        }
    }

    fn hir(&self, package_id: PackageId) -> &Hir {
        if package_id == self.package_id {
            self.hir
        } else {
            &self.packages[package_id].hir
        }
    }

    fn discover_data(&self, package_id: PackageId) -> &DiscoverData {
        if package_id == self.package_id {
            self.discover_data
        } else {
            &self.packages[package_id].discover_data
        }
    }

    fn reso_ctx(&self) -> ResoCtx {
        *self.reso_ctxs.last().unwrap()
    }

    fn do_pre_typing(&mut self, ctx: HirVisitorCtx) {
        match ctx.kind {
            NodeKind::FnDecl => {
                let FnDecl {
                    name,
                    args,
                    ret_ty,
                    unsafe_,
                    body,
                    .. } = ctx.hir.fn_decl(ctx.node);
                if body.is_none() && unsafe_.is_none() {
                    self.error_span(ctx.node, name.span,
                        "external function must be marked as `unsafe`".into());
                }
                let args: Vec<_> = args.iter()
                    .copied()
                    .map(|n| self.build_type(n))
                    .collect();
                let result = ret_ty.map(|n| self.build_type(n))
                    .unwrap_or_else(|| self.primitive_type(PrimitiveType::Unit));
                self.insert_typing(ctx.node, TypeData::Fn(FnType {
                    args,
                    result,
                    unsafe_: unsafe_.is_some(),
                }));
            }
            NodeKind::Struct => {
                self.begin_typing(ctx.node);
            }
            | NodeKind::Block
            | NodeKind::FieldAccess
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
            | NodeKind::StructValueField
            | NodeKind::TyExpr
            | NodeKind::Use
            | NodeKind::While
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
                    name,
                    ret_ty,
                    body,
                    .. } = ctx.hir.fn_decl(ctx.node);
                let expected_ret_ty = ret_ty
                    .map(|n| self.unaliased_typing(n).id())
                    .unwrap_or(self.primitive_type(PrimitiveType::Unit));
                if let Some(body) = *body {
                    self.unify(self.check_data.typing(body), expected_ret_ty);
                    let actual_ret_ty = self.unaliased_typing(body).id();

                    if actual_ret_ty != expected_ret_ty {
                        let node = *ctx.hir.block(body).exprs.last().unwrap();
                        self.fatal(node, format!("mismatching return types: function `{fname}::{fargs}` expects `{exp}`, found `{act}`",
                            fname=name.value, fargs=FnArgsKey::from_decl(ctx.node, ctx.hir),
                            exp=self.display_type(expected_ret_ty),
                            act=self.display_type(actual_ret_ty)));
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
                        _ => self.check_data.typing(expr)
                    }
                } else {
                    self.primitive_type(PrimitiveType::Unit)
                }
            }
            NodeKind::FieldAccess => {
                let hir::FieldAccess { receiver, field } = ctx.hir.field_access(ctx.node);
                let struct_ty = self.check_data.typing(*receiver);
                self.resolve_struct_field(Some(*receiver), struct_ty, ctx.node, field)
                    .unwrap_or_else(|| self.primitive_type(PrimitiveType::Unit))
            }
            NodeKind::FnCall => self.type_fn_call(&ctx),
            NodeKind::FnDecl => {
                unreachable!()
            }
            NodeKind::FnDeclArg => {
                self.check_data.typing(ctx.hir.fn_decl_arg(ctx.node).ty)
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = ctx.hir.if_expr(ctx.node);
                let actual_cond_ty = self.unaliased_typing(cond);
                if !matches!(actual_cond_ty.data(), TypeData::Primitive(PrimitiveType::Bool)) {
                    self.fatal(cond, format!(
                        "invalid type of `if` condition: expected `bool`, found `{}`",
                        self.display_type(actual_cond_ty.id())));
                }
                let if_true_ty = self.check_data.typing(if_true);
                if let Some(if_false) = if_false {
                    let if_false_ty = self.check_data.typing(if_false);
                    self.unify(if_true_ty, if_false_ty);
                    let if_true_ty = self.unalias_type(if_true_ty).id();
                    let if_false_ty = self.unalias_type(if_false_ty).id();
                    if if_true_ty != if_false_ty {
                        self.fatal(ctx.node, format!("mismatching types of `if` arms: `{}`, `{}`",
                            self.display_type(if_true_ty),
                            self.display_type(if_false_ty)));
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
                        self.unify(self.check_data.typing(ty), self.check_data.typing(init));
                    }

                    let typ = self.check_data.typing(ty);
                    if let Some(init) = init {
                        let actual = self.unaliased_typing(init).id();
                        let expected = self.unalias_type(typ).id();
                        if actual != expected {
                            self.fatal(init, format!("mismatching types: expected `{}`, found `{}`",
                                self.display_type(expected), self.display_type(actual)));
                        }
                    }
                    typ
                } else if let Some(init) = init {
                    self.check_data.typing(init)
                } else {
                    self.fatal(ctx.node, "can't infer variable type".into())
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
                    Literal::Unit => self.primitive_type(PrimitiveType::Unit),
                    Literal::String(_) => self.primitive_type(PrimitiveType::String),
                    Literal::Char(_) => self.primitive_type(PrimitiveType::Char),
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
                self.check_data.typing(ctx.hir.struct_(ctx.node).ty)
            }
            NodeKind::StructType => {
                let fields = &ctx.hir.struct_type(ctx.node).fields;
                let named = ctx.hir.try_struct(self.discover_data.parent_of(ctx.node)).is_some();
                if named {
                    let fields: Vec<_> = fields
                        .iter()
                        .map(|f| self.check_data.typing(f.ty))
                        .collect();
                    self.insert_type(ctx.node, TypeData::Struct(StructType {
                        fields,
                    }))
                } else {
                    let fields: Vec<_> = fields
                        .iter()
                        .map(|f|
                            (f.name.clone().map(|v| v.value),
                            self.unaliased_typing(f.ty).id()))
                        .collect();
                    self.unnamed_struct(ctx.node, UnnamedStructKey::new(fields))
                }
            }
            NodeKind::StructValueField => {
                let value = ctx.hir.struct_value_field(ctx.node).value;
                self.check_data.typing(value)
            }
            NodeKind::Path => {
                if self.reso_ctx() == ResoCtx::Import {
                    return
                } else {
                    let segment = ctx.hir.path(ctx.node).segment;
                    let target = self.check_data.target_of(segment);
                    self.check_data.insert_path_to_target(ctx.node, target);
                    self.check_data.typing(segment)
                }
            }
            NodeKind::StructValue => {
                let StructValue { name, explicit_tuple, fields } = ctx.hir.struct_value(ctx.node);
                assert!(explicit_tuple.is_none() || !fields.is_empty());
                let ty = if let Some(name) = *name {
                    self.check_data.typing(name)
                } else {
                    if fields.is_empty() {
                        self.primitive_type(PrimitiveType::Unit)
                    } else {
                        let key = UnnamedStructKey::new(fields.iter()
                            .map(|&v| ctx.hir.struct_value_field(v))
                            .map(|v| (v.name.clone().map(|v| v.value),
                                self.unaliased_typing(v.value).id()))
                            .collect());
                        self.unnamed_struct(ctx.node, key)
                    }
                };
                for (i, &field_node) in fields.iter().enumerate() {
                    let field = ctx.hir.struct_value_field(field_node);
                    let f = if let Some(n) = &field.name {
                        n.span.spanned(Field::Ident(n.value.clone()))
                    } else {
                        ctx.hir.node_kind(field.value).span.spanned(Field::Index(i as u32))
                    };
                    let expected_ty = if let Some(v) = self.resolve_struct_field(None, ty, field_node, &f) {
                        v
                    } else {
                        continue;
                    };
                    // No point in checking types for unnamed struct since it's been defined by the
                    // actual types.
                    if name.is_some() {
                        let expected_ty = self.unalias_type(expected_ty).id();

                        self.unify(self.check_data.typing(field_node), expected_ty);
                        let actual_ty = self.unaliased_typing(field_node).id();

                        if expected_ty != actual_ty {
                            let text = format!(
                                "mismatching types in struct `{struct_ty}` field `{field}`: expected `{exp}`, found `{act}`",
                                struct_ty = self.display_type(ty),
                                field = f.value,
                                exp = self.display_type(expected_ty),
                                act = self.display_type(actual_ty));
                            self.fatal(field.value, text);
                        }
                    }
                }
                ty
            }
            NodeKind::PathEndIdent => self.type_path_end_ident(&ctx),
            NodeKind::PathSegment => {
                if_chain! {
                    if self.reso_ctx() != ResoCtx::Import;
                    if let Some(&suffix) = ctx.hir.path_segment(ctx.node).suffix.first();
                    then {
                        let target = self.check_data.target_of(suffix);
                        self.check_data.insert_path_to_target(ctx.node, target);
                        self.check_data.typing(suffix)
                    } else {
                        return;
                    }
                }
            }
            NodeKind::TyExpr => {
                let TyExpr { muta: _, data } = ctx.hir.ty_expr(ctx.node);
                match &data.value {
                    TyData::Array(_) => unimplemented!(),
                    &TyData::Ptr(_) => unimplemented!(),
                    TyData::Ref(_) => unimplemented!(),
                    TyData::Slice(_) => unimplemented!(),
                    | &TyData::Path(node)
                    | &TyData::Struct(node)
                    => {
                        self.check_data.typing(node)
                    }
                }
            }
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            | NodeKind::Use
            => {
                self.primitive_type(PrimitiveType::Unit)
            }
            NodeKind::While
            => {
                let cond = ctx.hir.while_(ctx.node).cond;
                let actual_cond_ty = self.unaliased_typing(cond);
                if !matches!(actual_cond_ty.data(), TypeData::Primitive(PrimitiveType::Bool)) {
                    self.fatal(cond, format!(
                        "invalid type of `while` condition: expected `bool`, found `{}`",
                        self.display_type(actual_cond_ty.id())));
                }
                self.primitive_type(PrimitiveType::Unit)
            },
            _ => unimplemented!("{:?}", ctx.hir.node_kind(ctx.node))
        };
        self.finish_typing(ctx.node, ty);
    }

    fn type_binary_op(&mut self, BinaryOp { kind, left, right }: BinaryOp, ctx: HirVisitorCtx) -> TypeId {
        self.unify(self.check_data.typing(left), self.check_data.typing(right));

        let left_ty = self.unaliased_typing(left);
        let right_ty = self.unaliased_typing(right);
        use BinaryOpKind::*;
        match kind.value {
            Assign => {
                if left_ty.id() != right_ty.id() {
                    self.fatal(right, format!(
                        "mismatching types: expected `{}`, found `{}`",
                        self.display_type(left_ty.id()),
                        self.display_type(right_ty.id())));
                }
                self.primitive_type(PrimitiveType::Unit)
            }
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
                    self.fatal_span(ctx.node, kind.span, format!(
                        "binary operation `{}` can't be applied to types `{}`, `{}`",
                        kind.value,
                        self.display_type(left_ty.id()),
                        self.display_type(right_ty.id())));
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
                    self.fatal_span(ctx.node, kind.span, format!(
                        "binary operation `{}` can't be applied to types `{}`, `{}`",
                        kind.value,
                        self.display_type(left_ty.id()),
                        self.display_type(right_ty.id())));
                }
                left_ty.id()
            }
            _ => todo!("{:?}", kind),
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
                    self.fatal_span(ctx.node, kind.span, format!(
                        "unary operation `{}` can't be applied to type `{}`",
                        kind.value, self.display_type(arg_ty.id())));
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
        let typ = self.check_data.type_mut(ty.1);
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
            let fallback = match self.check_data.type_(ty).data().as_unknown_number().unwrap() {
                NumberType::Int => i32,
                NumberType::Float => f64,
            };
            let typ = self.check_data.type_mut(ty);
            typ.data = Some(TypeData::Type(fallback));
        }
    }

    fn has_complete_typing(&self, node: NodeId) -> bool {
        let id = if let Some(v) = self.check_data.try_typing(node) {
            v
        } else {
            return false;
        };
        if id.0 == self.package_id {
            self.check_data.type_(id.1).data.is_some()
        } else {
            debug_assert!(self.type_(id).data.is_some());
            true
        }
    }

    fn resolve_struct_field(&mut self,
        receiver: Option<NodeId>,
        struct_ty: TypeId,
        field_node: NodeId,
        field: &S<Field>,
    ) -> Option<TypeId> {
        let (idx, ty) = {
            let struct_ty = self.unalias_type(struct_ty);
            let field_tys = if let Some(StructType { fields }) = struct_ty.data().as_struct() {
                fields
            } else {
                self.fatal(receiver.unwrap(), format!(
                    "expected expression of struct type, found `{}`",
                    self.display_type(struct_ty.id())));
                return None;
            };

            let struct_hir = self.hir(struct_ty.package_id);
            // TODO This is inefficient as the method is going to be called often for field accesses.
            let field_count;
            let field_names: HashMap<_, _> = match struct_hir.node_kind(struct_ty.node).value {
                NodeKind::StructType => {
                    let fields = &struct_hir.struct_type(struct_ty.node).fields;
                    field_count = fields.len();
                    fields.iter().enumerate()
                        .filter_map(|(i, f)| f.name.clone().map(|n| (n.value, i)))
                        .collect()
                }
                NodeKind::StructValue => {
                    let fields = &struct_hir.struct_value(struct_ty.node).fields;
                    field_count = fields.len();
                    fields.iter().enumerate()
                        .map(|(i, &v)| (i, self.hir.struct_value_field(v)))
                        .filter_map(|(i, f)| f.name.clone().map(|n| (n.value, i)))
                        .collect()
                }
                _ => unreachable!()
            };

            let idx = match &field.value {
                Field::Ident(ident) => {
                    if let Some(&i) = field_names.get(ident) {
                        i as u32
                    } else {
                        self.fatal_span(field_node, field.span, format!(
                            "unknown field `{}` on struct `{}`",
                            ident, self.display_type(struct_ty.id())));
                        return None;
                    }
                }
                &Field::Index(i) => {
                    if !field_names.is_empty() || i as usize >= field_count {
                        self.fatal_span(field_node, field.span, format!(
                            "unknown field `{}` on struct `{}`",
                            i, self.display_type(struct_ty.id())));
                        return None;
                    }
                    i
                }
            };
            (idx, field_tys[idx as usize])
        };
        assert!(self.check_data.struct_fields.insert(field_node, idx).is_none());
        Some(ty)
    }

    fn unnamed_struct(&mut self, node: NodeId, key: UnnamedStructKey) -> TypeId {
        if let Some(&ty) = self.unnamed_structs.get(&key) {
            ty
        } else {
            let ty = self.insert_type(node, TypeData::Struct(StructType {
                fields: key.field_types(),
            }));
            assert_eq!(ty.0, self.package_id);
            self.unnamed_structs.insert(key.clone(), ty);
            self.check_data.unnamed_structs.insert(key, ty.1);
            ty
        }
    }

    fn error(&self, node: NodeId, text: String) -> TypeId {
        let span = self.hir.node_kind(node).span;
        self.error_span(node, span, text)
    }

    fn error_span(&self, node: NodeId, span: Span, text: String) -> TypeId {
        let id = {
            let mut n = node;
            loop {
                n = self.discover_data.module_of(n);
                if let Some(id) = self.hir.module(n).source_id {
                    break id;
                }
            }
        };

        self.diag.borrow_mut().report(diag::Report {
            severity: Severity::Error,
            text,
            source: Some(diag::Source {
                id,
                span,
            })
        });

        self.errors.borrow_mut().has = true;
        self.primitive_type(PrimitiveType::Unit)
    }

    fn fatal(&self, node: NodeId, text: String) -> TypeId {
        let span = self.hir.node_kind(node).span;
        self.fatal_span(node, span, text)
    }

    fn fatal_span(&self, node: NodeId, span: Span, text: String) -> TypeId {
        let r = self.error_span(node, span, text);
        if let Some(fn_decl) = self.discover_data.try_fn_decl_of(node) {
            self.errors.borrow_mut().fatal_in_fn_decls.insert(fn_decl, ());
        } else {
            self.errors.borrow_mut().fatal_in_mod = true;
        }
        r
    }

    fn display_type<'a>(&'a self, ty: TypeId) -> impl std::fmt::Display + 'a {
        struct Display<'a> {
            this: &'a Impl<'a>,
            ty: TypeId,
        }
        impl std::fmt::Display for Display<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                self.this.display_type0(self.ty, f)
            }
        }
        Display {
            this: self,
            ty,
        }
    }

    fn display_type0(&self, ty: TypeId, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        self.display_type1(self.type_(ty), f)
    }

    fn display_type1(&self, ty: &Type, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &ty.data {
            Some(v) => {
                match v {
                    TypeData::Fn(FnType { args, result, unsafe_ }) => {
                        if *unsafe_ {
                            write!(f, "unsafe ")?;
                        }
                        write!(f, "fn(")?;
                        for (i, &arg) in args.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            self.display_type0(arg, f)?;
                        }
                        write!(f, ")")?;
                        if !matches!(self.type_(*result).data().as_primitive(), Some(PrimitiveType::Unit)) {
                            write!(f, " -> ")?;
                            self.display_type0(*result, f)?;
                        }
                        Ok(())
                    }
                    &TypeData::Primitive(v) => write!(f, "{}", v),
                    TypeData::Struct(StructType { fields: field_tys }) => {
                        if let Some(Struct { name , ty_args, .. }) = self.hir.try_struct(self.discover_data.parent_of(ty.node)) {
                            write!(f, "{}", name.value)?;
                            if !ty_args.is_empty() {
                                todo!();
                            }
                        } else if let Some(hir::StructType { fields }) = self.hir.try_struct_type(ty.node) {
                            assert_eq!(fields.len(), field_tys.len());
                            let mut fields: Vec<_> = fields.iter().zip(field_tys.iter())
                                .map(|(f, ty)| (f.name.as_ref().map(|v| v.value.clone()), *ty))
                                .collect();
                            let tuple = fields.first().map(|(n, _)| n.is_some()) != Some(true);
                            if !tuple {
                                fields.sort_by(|(n1, _), (n2, _)| n1.as_ref().unwrap().cmp(n2.as_ref().unwrap()));
                            }
                            write!(f, "{{")?;
                            for (i, (name, ty)) in fields.iter().enumerate() {
                                if i > 0 {
                                    write!(f, ", ")?;
                                }
                                if let Some(name) = name {
                                    write!(f, "{}: ", name)?;
                                }
                                self.display_type0(*ty, f)?;
                            }
                            if tuple && fields.len() == 1 {
                                write!(f, ",")?;
                            }
                            write!(f, "}}")?;
                        } else {
                            let fields = &self.hir.struct_value(ty.node).fields;
                            // TODO can this be deduped with hir::StructType code above?
                            assert_eq!(fields.len(), field_tys.len());
                            let mut fields: Vec<_> = fields.iter().zip(field_tys.iter())
                                .map(|(&f, &ty)| (self.hir.struct_value_field(f).name.as_ref().map(|v| v.value.clone()), ty))
                                .collect();
                            let tuple = fields.first().map(|(n, _)| n.is_some()) != Some(true);
                            if !tuple {
                                fields.sort_by(|(n1, _), (n2, _)| n1.as_ref().unwrap().cmp(n2.as_ref().unwrap()));
                            }
                            write!(f, "{{")?;
                            for (i, (name, ty)) in fields.iter().enumerate() {
                                if i > 0 {
                                    write!(f, ", ")?;
                                }
                                if let Some(name) = name {
                                    write!(f, "{}: ", name)?;
                                }
                                self.display_type0(*ty, f)?;
                            }
                            if tuple && fields.len() == 1 {
                                write!(f, ",")?;
                            }
                            write!(f, "}}")?;
                        }
                        Ok(())
                    }
                    &TypeData::Type(ty) => self.display_type0(ty, f),
                    &TypeData::UnknownNumber(v) => match v {
                        NumberType::Int => write!(f, "?integer"),
                        NumberType::Float => write!(f, "?float"),
                    }
                }
            }
            None => write!(f, "?unknown")
        }
    }

    fn type_fn_call(&mut self, ctx: &HirVisitorCtx) -> TypeId {
        let FnCall {
            callee,
            kind,
            args: actual_args,
            .. } = ctx.hir.fn_call(ctx.node);
        let (fn_decl_node, res) = {
            let callee_ty = self.unaliased_typing(*callee);
            if *kind != FnCallKind::Free {
                unimplemented!();
            }
            let res = if let Some(v) = callee_ty.data().as_fn() {
                v.result
            } else {
                return self.fatal(*callee, format!(
                    "invalid callee type: expected function, found `{}`",
                    self.display_type(callee_ty.id())));
            };
            let fn_decl_node = callee_ty.node();
            (fn_decl_node, res)
        };

        let expected_args = self.hir(fn_decl_node.0).fn_decl(fn_decl_node.1).args.clone();
        assert_eq!(actual_args.len(), expected_args.len());

        for (actual, &expected) in actual_args
            .iter()
            .zip(expected_args.iter())
        {
            self.unify(self.check_data.typing(actual.value), self.check_data(fn_decl_node.0).typing(expected));

            let expected_ty = self.unalias_type(self.check_data(fn_decl_node.0).typing(expected)).id();
            let actual_ty = self.unaliased_typing(actual.value).id();
            if actual_ty != expected_ty {
                let hir = self.hir(fn_decl_node.0);
                let name = &hir.fn_decl(fn_decl_node.1).name.value;
                self.fatal(actual.value, format!(
                    "mismatching types in fn call of `{fname}::{fargs}`: expected `{exp}`, found `{act}`",
                    fname=name, fargs=FnArgsKey::from_decl(fn_decl_node.1, hir),
                    exp=self.display_type(expected_ty), act=self.display_type(actual_ty)));
            }
        }

        res
    }

    fn describe_named(&self, node: GlobalNodeId) -> String {
        let hir = self.hir(node.0);
        let kind = hir.node_kind(node.1).value;
        match kind {
            NodeKind::FnDecl => format!("function `{}`", hir.fn_decl(node.1).name.value),
            NodeKind::LetDecl => format!("variable `{}`", hir.let_decl(node.1).name.value),
            NodeKind::Module => format!("module `{}`", hir.module(node.1).name.as_ref().unwrap().name.value),
            NodeKind::Struct => {
                let prim = if node.0.is_std() {
                    let cd = &self.packages[PackageId::std()].check_data;
                    let ty = cd.typing(node.1);
                    assert!(ty.0.is_std());
                    cd.type_(ty.1).data().as_primitive().is_some()
                } else {
                    false
                };
                let kind = if prim {
                    "primitive type"
                } else {
                    "struct type"
                };
                format!("{} `{}`", kind, hir.struct_(node.1).name.value)
            },
            _ => unreachable!("{:?}", kind),
        }
    }

    fn type_path_end_ident(&mut self, ctx: &HirVisitorCtx) -> TypeId {
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
            let kind = self.hir(node.0).node_kind(node.1).value;
            if is_valid_in_reso_ctx(kind, reso_ctx);
            then {
                node
            } else {
                let found = reso.type_or_other().unwrap();
                let found = self.describe_named(found);
                return if let Some(expected_ns_kind) = expected_ns_kind {
                    let exp_str = match expected_ns_kind {
                        NsKind::Type => "type expression",
                        NsKind::Value => "expression",
                    };
                    self.fatal(ctx.node, format!(
                        "expected {}, found {}", exp_str, found))
                } else {
                    self.fatal(ctx.node, format!("{} can't be imported", found))
                };
            }
        };
        if reso_ctx == ResoCtx::Import {
            return self.primitive_type(PrimitiveType::Unit);
        }
        self.check_data.insert_path_to_target(ctx.node, (pkg, node));
        if pkg == self.package_id {
            self.build_type(node)
        } else {
            self.packages[pkg].check_data.typing(node)
        }
    }
}

impl HirVisitor for Impl<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        if self.errors.borrow().fatal_in_mod {
            return;
        }
        if let Some(v) = reso_ctx(ctx.link) {
            self.reso_ctxs.push(v);
        }
        if self.check_data.try_typing(ctx.node).is_none() {
            self.do_pre_typing(ctx);
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        if self.errors.borrow().fatal_in_mod {
            return;
        }
        let has_fatal_fn_err = self.discover_data.try_fn_decl_of(ctx.node)
            .or_else(|| self.hir.try_fn_decl(ctx.node).map(|_| ctx.node))
            .map(|v| self.errors.borrow().fatal_in_fn_decls.contains_key(&v))
            .unwrap_or(false);
        if !has_fatal_fn_err {
            self.check(ctx);
            if !self.has_complete_typing(ctx.node) {
                self.do_typing(ctx);
            }
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
        | StructValue(StructValueLink::Field)
        | StructValue(StructValueLink::FieldValue)
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
        | StructValue(StructValueLink::Name)
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