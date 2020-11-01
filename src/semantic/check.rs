use enum_as_inner::EnumAsInner;
use if_chain::if_chain;
use slab::Slab;
use std::cell::RefCell;
use std::collections::{hash_map, HashMap, HashSet};

use crate::diag::DiagRef;
use crate::hir::{self, *};
use crate::hir::traverse::*;
use crate::package::{GlobalNodeId, PackageId, Packages, PackageKind};
use crate::util::iter::IteratorExt;

use super::*;
use discover::{DiscoverData, NsKind};
use resolve::{ResolutionKind, Resolver,ResolveData};

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

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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
        };
        write!(f, "{}", s)
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum LangType {
    String,
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
    pub params: Vec<TypeId>,
    pub result: TypeId,
    pub unsafe_: bool,
}

#[derive(Debug)]
pub struct StructTypeField {
    /// Original index of the field as defined in HIR.
    /// Record struct type will have the field order normalized.
    pub def_idx: u32,
    pub ty: TypeId,
}

#[derive(Debug)]
pub struct StructType {
    pub fields: Vec<StructTypeField>,
}

pub type LocalTypeId = usize;

pub type TypeId = (PackageId, LocalTypeId);

#[derive(Default)]
pub struct Std {
    primitive_types: HashMap<PrimitiveType, LocalTypeId>,
    lang_type_to_id: HashMap<LangType, LocalTypeId>,
    type_id_to_lang: HashMap<LocalTypeId, LangType>,
}

impl Std {
    pub fn primitive(&self, ty: PrimitiveType) -> LocalTypeId {
        self.primitive_types[&ty]
    }

    pub fn lang(&self, ty: LangType) -> LocalTypeId {
        self.lang_type_to_id[&ty]
    }

    pub fn lang_of(&self, ty: LocalTypeId) -> Option<LangType> {
        self.type_id_to_lang.get(&ty).copied()
    }
}

#[derive(Debug)]
enum ImplValueItem {
    Single(NodeId),
    Fns(Vec<NodeId>), // FnDef
}

#[derive(Debug, Default)]
struct Impl {
    values: HashMap<Ident, ImplValueItem>,
}

#[derive(Default)]
pub struct CheckData {
    types: Slab<Type>,
    typings: NodeMap<TypeId>,
    std: Option<Box<Std>>,
    path_to_target: NodeMap<GlobalNodeId>,
    /// Maps `FieldAccess` and `StructValueField` nodes to the field index on a struct type.
    /// Note the index may not correspond to index of HIR field, use `StructTypeField::def_idx`.
    struct_fields: NodeMap<u32>,
    /// Unnamed tuple and record structs defined in this package.
    unnamed_structs: HashMap<UnnamedStructKey, LocalTypeId>,
    lvalues: NodeMap<()>,
    /// Impls defined in this package.
    impls: HashMap<TypeId, Vec<Impl>>,
    entry_point: Option<NodeId>,
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

    pub fn std(&self) -> &Std {
        &*self.std.as_ref().unwrap()
    }

    pub fn target_of(&self, path: NodeId) -> GlobalNodeId {
        self.path_to_target[&path]
    }

    pub fn try_target_of(&self, path: NodeId) -> Option<GlobalNodeId> {
        self.path_to_target.get(&path).copied()
    }

    fn insert_path_to_target(&mut self, path: NodeId, target: GlobalNodeId) {
        assert!(self.path_to_target.insert(path, target).is_none());
    }

    pub fn struct_field(&self, node: NodeId) -> u32 {
        self.struct_fields[&node]
    }

    fn set_lvalue(&mut self, node: NodeId) {
        assert!(self.lvalues.insert(node, ()).is_none());
    }

    fn is_lvalue(&self, node: NodeId) -> bool {
        self.lvalues.contains_key(&node)
    }

    pub fn entry_point(&self) -> Option<NodeId> {
        self.entry_point
    }
}

#[derive(Debug)]
pub struct CheckError(());

pub struct Check<'a> {
    pub package_id: PackageId,
    pub package_name: &'a Ident,
    pub package_kind: PackageKind,
    pub hir: &'a Hir,
    pub discover_data: &'a DiscoverData,
    pub resolve_data: &'a ResolveData,
    pub packages: &'a Packages,
    pub diag: DiagRef<'a>,
}

impl<'a> Check<'a> {
    pub fn run(self) -> Result<CheckData, CheckError> {
        let mut check_data = CheckData::default();

        let mut unnamed_structs = HashMap::new();
        for package in self.packages.iter() {
            for (k, ty) in &package.check_data.unnamed_structs {
                // TODO How bad is this in terms of perf/mem?
                assert!(unnamed_structs.insert(k.clone(), (package.id, *ty)).is_none());
            }
        }

        let imp = &mut PassImpl {
            discover_data: self.discover_data,
            check_data: &mut check_data,
            unknown_num_types: Default::default(),
            package_id: self.package_id,
            package_name: self.package_name,
            package_kind: self.package_kind,
            packages: self.packages,
            reso_ctxs: Default::default(),
            #[cfg(debug_assertions)]
            type_id_set: Default::default(),
            unnamed_structs,
            hir: self.hir,
            diag: self.diag,
            failed_typings: Default::default(),
            resolve_data: self.resolve_data,
        };
        if self.package_id.is_std() {
            imp.build_lang_types();
        }
        let _ = imp.pre_check_impls();
        self.hir.traverse(imp);
        if !imp.failed_typings.is_empty() {
            let diag_empty = self.diag.borrow().reports().is_empty();
            if diag_empty {
                dbg!(self.package_id);
                for node in &imp.failed_typings {
                    dbg!(self.hir.node_kind(*node.0));
                }
            }
            assert!(!diag_empty, "{:?}", self.package_id);
        }
        imp.resolve_entry_point().map_err(|_| CheckError(()))?;
        if self.diag.borrow().error_count() > 0 {
            return Err(CheckError(()));
        }
        for (_, ty) in &check_data.types {
            assert!(ty.data.is_some(), "{:?} {:?}", ty, self.hir.node_kind(ty.node));
        }
        Ok(check_data)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResoCtx {
    Import,
    Type,
    Value,
}

impl ResoCtx {
    fn to_ns_kind(self) -> Option<NsKind> {
        match self {
            ResoCtx::Import => None,
            ResoCtx::Type => Some(NsKind::Type),
            ResoCtx::Value => Some(NsKind::Value),
        }
    }
}

#[derive(Clone, Eq, Debug, Hash, PartialEq)]
struct UnnamedStructKey(Vec<(Option<Ident>, TypeId)>);

impl UnnamedStructKey {
    /// Also returns fields in normalized order. For tuples this is the same as the input order.
    /// Allows for duplicate non-`None` names, preferring the first occurrence in the constructed key.
    fn new(fields: Vec<(Option<Ident>, TypeId)>) -> (Self, Vec<StructTypeField>) {
        #[derive(Clone)]
        struct Field {
            def_idx: u32,
            name: Option<Ident>,
            ty: TypeId,
        }
        let mut fields: Vec<_> = fields
            .into_iter()
            .enumerate()
            .map(|(def_idx, (name, ty))| Field {
                name,
                def_idx: def_idx as u32,
                ty,
            })
            .collect();
        fields.sort_by(|a, b| a.name.cmp(&b.name));
        let key_fields = fields.iter()
            .map(|Field { name, ty, .. }| (name.clone(), *ty))
            .collect();
        fields.dedup_by(|a, b| a.name.is_some() && a.name == b.name);
        let ty_fields = fields.iter()
            .cloned()
            .map(|Field { def_idx, ty, .. }| StructTypeField {
                def_idx,
                ty,
            })
            .collect();
        (Self(key_fields), ty_fields)
    }
}

struct PassImpl<'a> {
    discover_data: &'a DiscoverData,
    check_data: &'a mut CheckData,
    unknown_num_types: HashSet<LocalTypeId>,
    package_id: PackageId,
    package_name: &'a Ident,
    package_kind: PackageKind,
    packages: &'a Packages,
    reso_ctxs: Vec<ResoCtx>,
    #[cfg(debug_assertions)]
    type_id_set: RefCell<HashSet<TypeId>>,
    /// Unnamed record and tuple structs defined in all packages.
    unnamed_structs: HashMap<UnnamedStructKey, TypeId>,
    hir: &'a Hir,
    diag: DiagRef<'a>,
    failed_typings: NodeMap<()>,
    resolve_data: &'a ResolveData,
}

impl PassImpl<'_> {
    pub fn build_lang_types(&mut self) {
        assert!(self.package_id.is_std());

        let mut std = Std::default();

        {
            use PrimitiveType::*;
            for &(prim_ty, path) in &[
                (Bool, &["bool"][..]),
                (Char, &["char"][..]),
                (F32, &["f32"][..]),
                (F64, &["f64"][..]),
                (I8, &["i8"][..]),
                (U8, &["u8"][..]),
                (I16, &["i16"][..]),
                (U16, &["u16"][..]),
                (I32, &["i32"][..]),
                (U32, &["u32"][..]),
                (I64, &["i64"][..]),
                (U64, &["u64"][..]),
                (I128, &["i128"][..]),
                (U128, &["u128"][..]),
                (ISize, &["isize"][..]),
                (USize, &["usize"][..]),
                (Unit, &["Unit"][..]),
            ] {
                let (pkg, node) = self.resolver()
                    .resolve_in_package(path)
                    .unwrap()
                    .ns_nodes(NsKind::Type)
                    .exactly_one()
                    .unwrap();
                assert!(pkg.is_std());
                let (pkg, ty) = self.insert_typing(node, TypeData::Primitive(prim_ty));
                assert!(pkg.is_std());
                assert!(std.primitive_types.insert(prim_ty, ty).is_none());
            }
        }

        {
            use LangType::*;
            for &(lang_ty, path) in &[
                (String, &["string", "String"][..]),
            ] {
                let (pkg, node) = self.resolver()
                    .resolve_in_package(path)
                    .unwrap()
                    .ns_nodes(NsKind::Type)
                    .exactly_one()
                    .unwrap();
                assert!(pkg.is_std());
                let ty = self.ensure_typing(node).unwrap();
                assert!(ty.0.is_std());
                assert!(std.type_id_to_lang.insert(ty.1, lang_ty).is_none());
                assert!(std.lang_type_to_id.insert(lang_ty, ty.1).is_none());
            }
        }

        assert!(self.check_data.std.replace(Box::new(std)).is_none());
    }

    fn ensure_opt_typing(&mut self, node: NodeId) -> Result<Option<TypeId>, ()> {
        if self.failed_typings.contains_key(&node) {
            return Err(());
        }
        if let Some(ty) = self.check_data.try_typing(node) {
            Ok(Some(ty))
        } else {
            self.hir.traverse_from(node, self);
            if self.failed_typings.contains_key(&node) {
                return Err(());
            }
            Ok(if let Some(ty) = self.check_data.try_typing(node) {
                Some(self.type_(ty).id())
            } else {
                None
            })
        }
    }

    fn ensure_typing(&mut self, node: NodeId) -> Result<TypeId, ()> {
        self.ensure_opt_typing(node).transpose().unwrap()
    }

    fn ensure_typing_global(&mut self, node: GlobalNodeId) -> Result<TypeId, ()> {
        let r = if node.0 == self.package_id {
            self.ensure_typing(node.1)?
        } else {
            self.packages[node.0].check_data.typing(node.1)
        };
        Ok(self.type_(r).id())
    }

    fn check_data(&self, package_id: PackageId) -> &CheckData {
        if package_id == self.package_id {
            &self.check_data
        } else {
            &self.packages[package_id].check_data
        }
    }

    fn type_(&self, mut id: TypeId) -> &Type {
        #[cfg(debug_assertions)] {
            assert!(self.type_id_set.borrow_mut().is_empty());
        }
        let ty = loop {
            let ty = self.check_data(id.0).type_(id.1);
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
        debug_assert!(!self.failed_typings.contains_key(&node));
        let ty = self.insert_type(node, data);
        self.check_data.insert_typing(node, ty);
        ty
    }

    fn primitive_type(&self, ty: PrimitiveType) -> TypeId {
        (PackageId::std(), self.check_data(PackageId::std()).std().primitive(ty))
    }

    fn lang_type(&self, ty: LangType) -> TypeId {
        (PackageId::std(), self.check_data(PackageId::std()).std().lang(ty))
    }

    fn typing(&self, node: NodeId) -> Result<TypeId, ()> {
        if self.failed_typings.contains_key(&node) {
            return Err(());
        }
        let ty = self.check_data.typing(node);
        Ok(self.type_(ty).id())
    }

    fn begin_typing(&mut self, node: NodeId) -> TypeId {
        debug_assert!(!self.failed_typings.contains_key(&node));
        let ty = self.check_data.insert_type((self.package_id, node), None);
        self.check_data.insert_typing(node, ty);
        ty
    }

    fn insert_failed_typing(&mut self, node: NodeId) {
        assert!(!self.diag.borrow().reports().is_empty());
        assert!(self.failed_typings.insert(node, ()).is_none());
    }

    fn finish_typing(&mut self, node: NodeId, ty: Result<TypeId, ()>) {
        debug_assert!(!self.failed_typings.contains_key(&node));
        if ty.is_err() {
            self.insert_failed_typing(node);
        }
        if let Some(incomplete_ty) = self.check_data.try_typing(node) {
            assert_eq!(incomplete_ty.0, self.package_id);
            if let Ok(ty) = ty {
                let typ = self.check_data.type_mut(incomplete_ty.1);
                assert_eq!(typ.node(), (self.package_id, node));
                assert!(typ.data.replace(TypeData::Type(ty)).is_none());
            }
        } else if let Ok(ty) = ty {
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

    fn do_pre_typing(&mut self, ctx: HirVisitorCtx) -> Result<(), ()> {
        match ctx.kind {
            NodeKind::FnDef => {
                let FnDef {
                    name,
                    params,
                    ret_ty,
                    unsafe_,
                    body,
                    .. } = self.hir.fn_def(ctx.node);
                if body.is_none() && unsafe_.is_none() {
                    self.error_span(ctx.node, name.span,
                        "external function must be marked as `unsafe`".into());
                }
                let mut param_tys = Vec::with_capacity(params.len());
                let mut err = false;
                for &n in params {
                    if let Ok(ty) = self.ensure_typing(n) {
                        param_tys.push(ty);
                    } else {
                        err = true;
                    }
                }
                let result = if let Some(n) = *ret_ty {
                    self.ensure_typing(n)?
                } else {
                    self.primitive_type(PrimitiveType::Unit)
                };
                if err {
                    return Err(());
                }
                self.insert_typing(ctx.node, TypeData::Fn(FnType {
                    params: param_tys,
                    result,
                    unsafe_: unsafe_.is_some(),
                }));
            }
            NodeKind::Impl => {
                self.finish_typing(ctx.node, Ok(self.primitive_type(PrimitiveType::Unit)));

                let hir::Impl {
                    ty_params,
                    trait_,
                    for_,
                    items,
                } = self.hir.impl_(ctx.node);
                if !ty_params.is_empty() || trait_.is_some() {
                    todo!();
                }

                self.reso_ctxs.push(ResoCtx::Type);
                let struct_ty = self.ensure_typing(*for_);
                assert_eq!(self.reso_ctxs.pop().unwrap(), ResoCtx::Type);
                let struct_ty = struct_ty?;

                if struct_ty.0 != self.package_id {
                    self.error(*for_, "cannot define inherent `impl` for a type from outside of this package".into());
                    return Err(());
                }

                {
                    let struct_ty = self.type_(struct_ty);
                    match struct_ty.data() {
                        | TypeData::Primitive(_)
                        | TypeData::Struct(_)
                        => {}
                        TypeData::Fn(_) => {
                            self.error(*for_, format!(
                                "can't define inherent `impl` on {}",
                                self.describe_named(struct_ty.node())));
                            return Err(());
                        }
                        | TypeData::Type(_)
                        | TypeData::UnknownNumber(_)
                        => unreachable!(),
                    }
                }

                let mut dup_errs = Vec::new();
                let impl_ = &mut self.check_data.impls.entry(struct_ty)
                    .or_insert_with(|| vec![Default::default()])
                    [0];
                for &item in items {
                    match self.hir.node_kind(item).value {
                        NodeKind::FnDef => {
                            let name = &self.hir.fn_def(item).name;
                            let sign = self.discover_data.fn_def_signature(item);
                            match impl_.values.entry(name.value.clone()) {
                                hash_map::Entry::Occupied(mut e) => {
                                    match e.get_mut() {
                                        ImplValueItem::Single(_) => {
                                            dup_errs.push(item);
                                        }
                                        ImplValueItem::Fns(fns) => {
                                            debug_assert!(!fns.iter().any(|&n| n == item));
                                            let discover_data = self.discover_data;
                                            if fns.iter().any(|&n| discover_data.fn_def_signature(n) == sign) {
                                                dup_errs.push(item);
                                            } else {
                                                fns.push(item);
                                            }
                                        }
                                    }
                                }
                                hash_map::Entry::Vacant(e) => {
                                    e.insert(ImplValueItem::Fns(vec![item]));
                                }
                            };
                        }
                        _ => unreachable!(),
                    }
                }
                for node in dup_errs {
                    let name = &self.hir.fn_def(node).name;
                    let sign = self.discover_data.fn_def_signature(node);
                    self.error_span(node, name.span, format!(
                        "function `{}` is defined multiple times within inherent `impl`",
                        sign.display_with_name(&name.value)));
                }
            }
            | NodeKind::Struct
            | NodeKind::TypeAlias
            => {
                self.begin_typing(ctx.node);
            }
            | NodeKind::Block
            | NodeKind::FieldAccess
            | NodeKind::FnCall
            | NodeKind::FnDefParam
            | NodeKind::IfExpr
            | NodeKind::Let
            | NodeKind::LetDef
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
                unimplemented!("{:?}", self.hir.node_kind(ctx.node));
            },
        }
        Ok(())
    }

    fn check(&mut self, ctx: HirVisitorCtx) -> Result<(), ()> {
        match ctx.kind {
            NodeKind::FnDef => {
                let FnDef {
                    name,
                    ret_ty,
                    body,
                    .. } = self.hir.fn_def(ctx.node);
                let expected_ret_ty = if let Some(n) = *ret_ty {
                    self.typing(n)?
                } else {
                    self.primitive_type(PrimitiveType::Unit)
                };
                if let Some(body) = *body {
                    let (actual_ret_ty, expected_ret_ty) = self.unify(self.typing(body)?, expected_ret_ty);
                    if actual_ret_ty != expected_ret_ty {
                        let node = self.hir.block(body).exprs.last()
                            .copied().unwrap_or(body);
                        self.error(node, format!(
                            "mismatching return types: function `{fname}::{fsign}` expects `{exp}`, found `{act}`",
                            fname=name.value, fsign= FnParamsSignature::from_def(ctx.node, self.hir),
                            exp=self.display_type(expected_ret_ty),
                            act=self.display_type(actual_ret_ty)));
                    }
                    self.handle_unknown_num_types();
                }
            },
            _ => {},
        }
        Ok(())
    }

    fn do_typing(&mut self, ctx: HirVisitorCtx) -> Result<Option<TypeId>, ()> {
        let ty = match ctx.kind {
            NodeKind::Block => {
                if let Some(&expr) = self.hir.block(ctx.node).exprs.last() {
                    use NodeKind::*;
                    match self.hir.node_kind(expr).value {
                        | Impl
                        | Loop
                        | FnDef
                        | Module
                        | Struct
                        | Use
                        | While
                        => self.primitive_type(PrimitiveType::Unit),
                        _ => self.typing(expr)?
                    }
                } else {
                    self.primitive_type(PrimitiveType::Unit)
                }
            }
            NodeKind::FieldAccess => {
                self.check_data.set_lvalue(ctx.node);
                let hir::FieldAccess { receiver, field } = self.hir.field_access(ctx.node);
                let struct_ty = self.typing(*receiver)?;
                self.resolve_struct_field(struct_ty, ctx.node, field)?
            }
            NodeKind::FnCall => self.type_fn_call(&ctx)?,
            NodeKind::FnDef => return Err(()),
            NodeKind::FnDefParam => {
                self.check_data.set_lvalue(ctx.node);
                self.typing(self.hir.fn_def_param(ctx.node).ty)?
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = self.hir.if_expr(ctx.node);
                if let Ok(actual_cond_ty) = self.typing(cond) {
                    if actual_cond_ty != self.primitive_type(PrimitiveType::Bool) {
                        self.error(cond, format!(
                            "invalid type of `if` condition: expected `bool`, found `{}`",
                            self.display_type(actual_cond_ty)));
                    }
                }
                let if_true_ty = self.typing(if_true)?;
                if let Some(if_false) = if_false {
                    let if_false_ty = self.typing(if_false)?;
                    let (if_true_ty, if_false_ty) = self.unify(if_true_ty, if_false_ty);
                    let if_true_ty = self.type_(if_true_ty).id();
                    let if_false_ty = self.type_(if_false_ty).id();
                    if if_true_ty != if_false_ty {
                        self.error(ctx.node, format!("mismatching types of `if` arms: `{}`, `{}`",
                            self.display_type(if_true_ty),
                            self.display_type(if_false_ty)));
                    }
                }
                if_true_ty
            }
            NodeKind::Impl => unreachable!(),
            NodeKind::Let => {
                self.primitive_type(PrimitiveType::Bool)
            }
            NodeKind::LetDef => {
                self.check_data.set_lvalue(ctx.node);
                let &LetDef { ty, init, .. } = self.hir.let_def(ctx.node);
                if let Some(ty) = ty {
                    let ty = self.typing(ty)?;
                    if let Some(init) = init {
                        let (exp, act) = self.unify(ty, self.typing(init)?);
                        if act != exp {
                            self.error(init, format!("mismatching types: expected `{}`, found `{}`",
                                self.display_type(exp), self.display_type(act)));
                        }
                        act
                    } else {
                        ty
                    }
                } else if let Some(init) = init {
                    self.typing(init)?
                } else {
                    self.error(ctx.node, "can't infer variable type".into());
                    return Err(());
                }
            }
            NodeKind::Literal => {
                match self.hir.literal(ctx.node) {
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
                    Literal::String(_) => self.lang_type(LangType::String),
                    Literal::Char(_) => self.primitive_type(PrimitiveType::Char),
                }
            }
            NodeKind::Module => return Ok(None),
            NodeKind::Op => {
                match self.hir.op(ctx.node) {
                    &Op::Binary(op) => {
                        self.type_binary_op(op, ctx)?
                    }
                    &Op::Unary(op) => {
                        self.type_unary_op(op, ctx)?
                    }
                }
            }
            NodeKind::Path => {
                let segment = self.hir.path(ctx.node).segment;
                if self.failed_typings.contains_key(&segment) {
                    return Err(())
                } else if let Some(target) = self.check_data.try_target_of(segment) {
                    if self.check_data(target.0).is_lvalue(target.1) {
                        self.check_data.set_lvalue(ctx.node);
                    }
                    self.check_data.insert_path_to_target(ctx.node, target);
                    self.typing(segment)?
                } else {
                    return Ok(None);
                }
            }
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            => return self.resolve_path(&ctx),
            NodeKind::PathEndIdent => {
                // Check `use {self}` case.
                if self.discover_data.find_use_node(ctx.node, self.hir).is_some() {
                    let ident = &self.hir.path_end_ident(ctx.node).item.ident;
                    if ident.value.is_self_lower()
                        && self.hir.path_segment(self.discover_data.parent_of(ctx.node)).prefix.is_empty()
                    {
                        self.error_span(ctx.node, ident.span,
                            "`self` import can only be used in path with prefix".into());
                        return Ok(None)
                    }
                }
                return if self.discover_data.find_method_call(ctx.node, self.hir).is_none() {
                    self.resolve_path(&ctx)
                } else {
                    Ok(None)
                };
            },
            NodeKind::PathSegment => {
                let suffix = &self.hir.path_segment(ctx.node).suffix;
                if suffix.len() == 1 {
                    if self.failed_typings.contains_key(&suffix[0]) {
                        return Err(())
                    } else if let Some(target) = self.check_data.try_target_of(suffix[0]) {
                        self.check_data.insert_path_to_target(ctx.node, target);
                        self.typing(suffix[0])?
                    } else {
                        return Ok(None);
                    }
                } else {
                    return Ok(None);
                }
            }
            NodeKind::Struct => {
                self.typing(self.hir.struct_(ctx.node).ty)?
            }
            NodeKind::StructType => {
                let fields = &self.hir.struct_type(ctx.node).fields;
                let named = self.hir.try_struct(self.discover_data.parent_of(ctx.node)).is_some();

                let mut seen_fields = HashSet::new();
                let mut dup_fields = HashSet::new();
                for (i, f) in fields.iter().enumerate() {
                    if let Some(name) = f.name.as_ref() {
                        if !seen_fields.insert(&name.value) {
                            if dup_fields.insert(i as u32) {
                                self.error_span(ctx.node, name.span, format!(
                                "field `{}` is defined multiple times",
                                name.value));
                            }
                        }
                    }
                }

                if named {
                    let mut field_tys = Vec::with_capacity(fields.len());
                    let mut err = false;
                    for (def_idx, f) in fields.iter().enumerate() {
                        let def_idx = def_idx as u32;
                        if let Ok(ty) = self.typing(f.ty) {
                            if !dup_fields.contains(&def_idx) {
                                field_tys.push(StructTypeField {
                                    def_idx,
                                    ty,
                                });
                            }
                        } else {
                            err = true;
                        }
                    }
                    if err {
                        return Err(());
                    }
                    self.insert_type(ctx.node, TypeData::Struct(StructType {
                        fields: field_tys,
                    }))
                } else {
                    let mut field_tys = Vec::with_capacity(fields.len());
                    let mut err = false;
                    for f in fields {
                        if let Ok(ty) = self.typing(f.ty) {
                            field_tys.push((f.name.clone().map(|v| v.value), ty));
                        } else {
                            err = true;
                        }
                    }
                    if err {
                        return Err(());
                    }
                    self.unnamed_struct(ctx.node, field_tys)
                }
            }
            NodeKind::StructValueField => {
                let value = self.hir.struct_value_field(ctx.node).value;
                self.typing(value)?
            }
            NodeKind::StructValue => {
                let StructValue { name, explicit_tuple, fields } = self.hir.struct_value(ctx.node);
                assert!(explicit_tuple.is_none() || !fields.is_empty());
                let ty = if let Some(name) = *name {
                    self.typing(name)?
                } else {
                    if fields.is_empty() {
                        self.primitive_type(PrimitiveType::Unit)
                    } else {
                        let mut field_tys = Vec::with_capacity(fields.len());
                        let mut err = false;
                        for &field in fields {
                            let f = self.hir.struct_value_field(field);
                            if let Ok(ty) = self.typing(f.value) {
                                field_tys.push((f.name.clone().map(|v| v.value), ty));
                            } else {
                                err = true;
                            }
                        }
                        if err {
                            return Err(());
                        }
                        self.unnamed_struct(ctx.node, field_tys)
                    }
                };
                let mut seen_fields = HashSet::new();
                for (i, &field_node) in fields.iter().enumerate() {
                    let field = self.hir.struct_value_field(field_node);
                    let f = if let Some(n) = &field.name {
                        n.span.spanned(Field::Ident(n.value.clone()))
                    } else {
                        self.hir.node_kind(field.value).span.spanned(Field::Index(i as u32))
                    };
                    let expected_ty = if let Ok(v) = self.resolve_struct_field(ty, field_node, &f) {
                        v
                    } else {
                        continue;
                    };

                    if !seen_fields.insert(self.check_data.struct_fields[&field_node]) {
                        let name = field.name.as_ref().unwrap();
                        self.error_span(field_node, name.span, format!(
                            "field `{}` is initialized multiple times",
                            name.value));
                        continue;
                    }

                    // No point in checking field types for unnamed struct since it's been defined
                    // by the actual types.
                    if name.is_none() {
                        continue;
                    }

                    let actual_ty = if let Ok(ty) = self.typing(field_node) {
                        ty
                    } else {
                        continue;
                    };
                    let (actual_ty, expected_ty) = self.unify(actual_ty, expected_ty);

                    if expected_ty != actual_ty {
                        let text = format!(
                            "mismatching types in struct `{struct_ty}` field `{field}`: expected `{exp}`, found `{act}`",
                            struct_ty = self.display_type(ty),
                            field = f.value,
                            exp = self.display_type(expected_ty),
                            act = self.display_type(actual_ty));
                        self.error(field.value, text);
                    }
                }

                let expected_field_count = match self.type_(ty).data() {
                    TypeData::Primitive(PrimitiveType::Unit) => 0,
                    TypeData::Struct(StructType { fields }) => fields.len(),
                    _ => unreachable!(),
                };
                if seen_fields.len() != expected_field_count {
                    // We got less fields than needed.
                    assert!(seen_fields.len() < expected_field_count);
                    let mut missing_fields = Vec::new();
                    let ty = self.type_(ty);
                    let struct_ty_def = self.hir.struct_type(ty.node);
                    if struct_ty_def.fields[0].name.is_some() {
                        for (i, f) in ty.data().as_struct().unwrap().fields.iter().enumerate() {
                            if seen_fields.contains(&(i as u32)) {
                                continue;
                            }
                            let name = struct_ty_def.fields[f.def_idx as usize].name.as_ref().unwrap();
                            missing_fields.push(name.value.as_ref());
                        }
                        missing_fields.sort();
                        self.error(ctx.node, format!(
                            "missing field{} {} in initializer of struct `{}`",
                            if missing_fields.len() > 1 { "s" } else { "" },
                            missing_fields.into_iter().map(|s| format!("`{}`", s)).collect::<Vec<_>>().join(", "),
                            self.display_type(ty.id())));
                    } else {
                        self.error(ctx.node, format!(
                            "missing field{} in initializer of tuple struct `{}`: expected {} field{}",
                            if expected_field_count > 1 { "s" } else { "" },
                            self.display_type(ty.id()),
                            expected_field_count, if expected_field_count > 1 { "s" } else { "" }));
                    }
                }

                ty
            }
            NodeKind::TyExpr => {
                let TyExpr { muta: _, data } = self.hir.ty_expr(ctx.node);
                match &data.value {
                    TyData::Array(_) => unimplemented!(),
                    &TyData::Ptr(_) => unimplemented!(),
                    TyData::Ref(_) => unimplemented!(),
                    TyData::Slice(_) => unimplemented!(),
                    | &TyData::Path(node)
                    | &TyData::Struct(node)
                    => {
                        self.typing(node)?
                    }
                }
            }
            NodeKind::TypeAlias => {
                let TypeAlias { vis: _, name: _, ty_params, ty } = self.hir.type_alias(ctx.node);
                if !ty_params.is_empty() {
                    todo!();
                }
                self.typing(*ty)?
            }
            NodeKind::Use => self.primitive_type(PrimitiveType::Unit),
            NodeKind::While
            => {
                let cond = self.hir.while_(ctx.node).cond;
                if let Ok(actual_cond_ty) = self.typing(cond) {
                    if actual_cond_ty != self.primitive_type(PrimitiveType::Bool) {
                        self.error(cond, format!(
                            "invalid type of `while` condition: expected `bool`, found `{}`",
                            self.display_type(actual_cond_ty)));
                    }
                }
                self.primitive_type(PrimitiveType::Unit)
            },
            _ => unimplemented!("{:?}", self.hir.node_kind(ctx.node))
        };
        Ok(Some(ty))
    }

    fn type_binary_op(&mut self, BinaryOp { kind, left, right }: BinaryOp, ctx: HirVisitorCtx) -> Result<TypeId, ()> {
        let (left_ty, right_ty) = self.unify(self.typing(left)?, self.typing(right)?);
        let left_ty = self.type_(left_ty);
        let right_ty = self.type_(right_ty);

        use BinaryOpKind::*;
        let ty = match kind.value {
            Assign => {
                if !self.check_data.is_lvalue(left) {
                    self.error(left, "can't assign to this expression".into());
                } else if left_ty.id() != right_ty.id() {
                    self.error(right, format!(
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
                    self.error_span(ctx.node, kind.span, format!(
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
                    self.error_span(ctx.node, kind.span, format!(
                        "binary operation `{}` can't be applied to types `{}`, `{}`",
                        kind.value,
                        self.display_type(left_ty.id()),
                        self.display_type(right_ty.id())));
                    return Err(());
                }
                left_ty.id()
            }
            _ => todo!("{:?}", kind),
        };
        Ok(ty)
    }

    fn type_unary_op(&mut self, UnaryOp { kind, arg }: UnaryOp, ctx: HirVisitorCtx) -> Result<TypeId, ()> {
        let arg_ty = self.type_(self.typing(arg)?);
        use UnaryOpKind::*;
        let ty = match kind.value {
            Neg => {
                let ok = match arg_ty.data() {
                    TypeData::Primitive(prim) if prim.as_number().is_some() => true,
                    TypeData::UnknownNumber(_) => true,
                    _ => false,
                };
                if !ok {
                    self.error_span(ctx.node, kind.span, format!(
                        "unary operation `{}` can't be applied to type `{}`",
                        kind.value, self.display_type(arg_ty.id())));
                    return Err(());
                }
                arg_ty.id()
            }
            _ => todo!(),
        };
        Ok(ty)
    }

    fn unify(&mut self, ty1: TypeId, ty2: TypeId) -> (TypeId, TypeId) {
        if ty1 == ty2 {
            return (ty1, ty2);
        }
        let (ty, to_type) = {
            let ty1 = self.type_(ty1);
            if ty1.id() == ty2 {
                return (ty2, ty2);
            }
            let ty2 = self.type_(ty2);
            if ty1.id() == ty2.id() {
                return (ty1.id(), ty1.id());
            }
            use TypeData::*;
            match (ty1.data(), ty2.data()) {
                (&UnknownNumber(num), Primitive(pt)) if pt.as_number() == Some(num) => (ty1.id(), ty2.id()),
                (Primitive(pt), &UnknownNumber(num)) if pt.as_number() == Some(num) => (ty2.id(), ty1.id()),
                (UnknownNumber(l), UnknownNumber(r)) if l == r => (ty1.id(), ty2.id()),
                _ => return (ty1.id(), ty2.id()),
            }
        };
        assert_eq!(ty.0, self.package_id);
        let typ = self.check_data.type_mut(ty.1);
        assert!(typ.data().as_unknown_number().is_some());
        assert!(self.unknown_num_types.remove(&ty.1));
        typ.data = Some(TypeData::Type(to_type));
        (to_type, to_type)
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

    fn has_complete_typing(&self, node: NodeId) -> Result<bool, ()> {
        if self.failed_typings.contains_key(&node) {
            return Err(());
        }
        let id = if let Some(v) = self.check_data.try_typing(node) {
            v
        } else {
            return Ok(false);
        };
        Ok(if id.0 == self.package_id {
            self.check_data.type_(id.1).data.is_some()
        } else {
            debug_assert!(self.type_(id).data.is_some());
            true
        })
    }

    fn resolve_struct_field(&mut self,
        struct_ty: TypeId,
        field_node: NodeId,
        field: &S<Field>,
    ) -> Result<TypeId, ()> {
        let (idx, ty) = {
            let struct_ty = self.type_(struct_ty);
            let ty_fields = if let TypeData::Struct(StructType { fields }) = struct_ty.data() {
                &fields[..]
            } else {
                &[]
            };

            let struct_hir = self.hir(struct_ty.package_id);
            // TODO This is inefficient as the method is going to be called often for field accesses.
            let field_count;
            let field_names: HashMap<_, _> = if !ty_fields.is_empty() {
                match struct_hir.node_kind(struct_ty.node).value {
                    NodeKind::StructType => {
                        let def_fields = &struct_hir.struct_type(struct_ty.node).fields;
                        field_count = def_fields.len();
                        ty_fields.iter().enumerate()
                            .filter_map(|(i, &StructTypeField { def_idx, .. })| {
                                let def_field = &def_fields[def_idx as usize];
                                def_field.name.clone().map(|n| (n.value, i))
                            })
                            .collect()
                    }
                    NodeKind::StructValue => {
                        let def_fields = &struct_hir.struct_value(struct_ty.node).fields;
                        field_count = def_fields.len();
                        ty_fields.iter().enumerate()
                            .filter_map(|(i, &StructTypeField { def_idx, .. })| {
                                let def_field = def_fields[def_idx as usize];
                                let def_field = self.hir.struct_value_field(def_field);
                                def_field.name.clone().map(|n| (n.value, i))
                            })
                            .collect()
                    }
                    _ => unreachable!(),
                }
            } else {
                field_count = 0;
                Default::default()
            };

            let idx = match &field.value {
                Field::Ident(ident) => {
                    if let Some(&i) = field_names.get(ident) {
                        i as u32
                    } else {
                        self.error_span(field_node, field.span, format!(
                            "unknown field `{}` on type `{}`",
                            ident, self.display_type(struct_ty.id())));
                        return Err(());
                    }
                }
                &Field::Index(i) => {
                    if !field_names.is_empty() || i as usize >= field_count {
                        self.error_span(field_node, field.span, format!(
                            "unknown field `{}` on type `{}`",
                            i, self.display_type(struct_ty.id())));
                        return Err(());
                    }
                    i
                }
            };
            (idx, ty_fields[idx as usize].ty)
        };
        assert!(self.check_data.struct_fields.insert(field_node, idx).is_none());
        Ok(ty)
    }

    fn unnamed_struct(&mut self, node: NodeId, fields: Vec<(Option<Ident>, TypeId)>) -> TypeId {
        let (key, fields) = UnnamedStructKey::new(fields);
        if let Some(&ty) = self.unnamed_structs.get(&key) {
            ty
        } else {
            let ty = self.insert_type(node, TypeData::Struct(StructType {
                fields,
            }));
            assert_eq!(ty.0, self.package_id);
            self.unnamed_structs.insert(key.clone(), ty);
            self.check_data.unnamed_structs.insert(key, ty.1);
            ty
        }
    }

    fn error(&self, node: NodeId, text: String) {
        let span = self.hir.node_kind(node).span;
        self.error_span(node, span, text);
    }

    fn error_span(&self, node: NodeId, span: Span, text: String) {
        self.diag.borrow_mut().error_span(self.hir, self.discover_data, node, span, text);
    }

    fn display_type<'a>(&'a self, ty: TypeId) -> impl std::fmt::Display + 'a {
        struct Display<'a> {
            this: &'a PassImpl<'a>,
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
        let hir = self.hir(ty.node().0);
        match &ty.data {
            Some(v) => {
                match v {
                    TypeData::Fn(FnType { params, result, unsafe_ }) => {
                        if *unsafe_ {
                            write!(f, "unsafe ")?;
                        }
                        write!(f, "fn(")?;
                        for (i, &param) in params.iter().enumerate() {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            self.display_type0(param, f)?;
                        }
                        write!(f, ")")?;
                        if !matches!(self.type_(*result).data().as_primitive(), Some(PrimitiveType::Unit)) {
                            write!(f, " -> ")?;
                            self.display_type0(*result, f)?;
                        }
                        Ok(())
                    }
                    &TypeData::Primitive(v) => write!(f, "{}", v),
                    TypeData::Struct(StructType { fields: ty_fields }) => {
                        if let Some(Struct { name , ty_params, .. }) = hir.try_struct(self.discover_data(ty.node().0).parent_of(ty.node().1)) {
                            write!(f, "{}", name.value)?;
                            if !ty_params.is_empty() {
                                todo!();
                            }
                        } else if let Some(hir::StructType { fields: def_fields }) = hir.try_struct_type(ty.node().1) {
                            assert!(def_fields.len() >= ty_fields.len());
                            let mut fields: Vec<_> = ty_fields.iter()
                                .map(|ty_field| {
                                    let def_field = &def_fields[ty_field.def_idx as usize];
                                    (def_field.name.as_ref().map(|v| v.value.clone()), ty_field.ty)
                                })
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
                            let def_fields = &hir.struct_value(ty.node().1).fields;
                            // TODO can this be deduped with hir::StructType code above?
                            assert_eq!(def_fields.len(), ty_fields.len());
                            let mut fields: Vec<_> = ty_fields.iter()
                                .map(|ty_field| {
                                    let def_field = def_fields[ty_field.def_idx as usize];
                                    let name = hir.struct_value_field(def_field).name.as_ref().map(|v| v.value.clone());
                                    (name, ty_field.ty)
                                })
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
                        NumberType::Int => write!(f, "<integer>"),
                        NumberType::Float => write!(f, "<float>"),
                    }
                }
            }
            None => write!(f, "<unknown>")
        }
    }

    fn type_fn_call(&mut self, ctx: &HirVisitorCtx) -> Result<TypeId, ()> {
        let FnCall {
            callee,
            kind,
            params: actual_params,
            .. } = self.hir.fn_call(ctx.node);
        let (fn_def_node, res_ty) = match *kind {
            FnCallKind::Free => {
                let callee_ty = self.type_(self.typing(*callee)?);
                let ty = if let Some(v) = callee_ty.data().as_fn() {
                    v.result
                } else {
                    self.error(*callee, format!(
                        "invalid callee type: expected function, found `{}`",
                        self.display_type(callee_ty.id())));
                    return Err(());
                };
                let fn_def_node = callee_ty.node();
                (fn_def_node, ty)
            }
            FnCallKind::Method => {
                let (fn_def, fn_ty) = self.resolve_method_call(ctx.node)?;
                let res_ty = self.type_(fn_ty).data().as_fn().unwrap().result;
                (fn_def, res_ty)
            }
        };

        let expected_params = self.hir(fn_def_node.0).fn_def(fn_def_node.1).params.clone();
        assert_eq!(actual_params.len(), expected_params.len());

        for (actual, &expected) in actual_params
            .iter()
            .zip(expected_params.iter())
        {
            let actual_ty = if let Ok(ty) = self.typing(actual.value) {
                ty
            } else {
                continue;
            };
            let expected_ty = self.check_data(fn_def_node.0).typing(expected);
            let (actual_ty, expected_ty) = self.unify(actual_ty, expected_ty);
            if actual_ty != expected_ty {
                let hir = self.hir(fn_def_node.0);
                let name = &hir.fn_def(fn_def_node.1).name.value;
                self.error(actual.value, format!(
                    "mismatching types in fn call of `{fname}::{fsign}`: expected `{exp}`, found `{act}`",
                    fname=name, fsign= FnParamsSignature::from_def(fn_def_node.1, hir),
                    exp=self.display_type(expected_ty), act=self.display_type(actual_ty)));
            }
        }

        Ok(res_ty)
    }

    fn describe_named(&self, node: GlobalNodeId) -> String {
        let hir = self.hir(node.0);
        let kind = hir.node_kind(node.1).value;
        if kind == NodeKind::Struct {
            let prim = if node.0.is_std() && !self.package_id.is_std() {
                let cd = &self.packages[PackageId::std()].check_data;
                let ty = cd.typing(node.1);
                assert!(ty.0.is_std());
                cd.type_(ty.1).data().as_primitive().is_some()
            } else {
                false
            };
            if prim {
                let name = self.discover_data(node.0).name(node.1, hir).unwrap();
                return format!("primitive type `{}`", name.value);
            }
        }
        self.discover_data(node.0).describe_named(node.1, hir).unwrap()
    }

    fn resolve_path(&mut self, ctx: &HirVisitorCtx) -> Result<Option<TypeId>, ()> {
        let reso = self.resolver().resolve_node(ctx.node)?;

        match reso.kind() {
            ResolutionKind::Exact => {}
            ResolutionKind::Empty => return Ok(None),
            ResolutionKind::Wildcard => {
                if !reso.nodes()
                    .all(|(_, (pkg, _))| pkg == self.package_id)
                {
                    self.error(ctx.node,
                        "only symbols from current package can be imported by wildcard import".into());
                }
                return Ok(None);
            }
            ResolutionKind::Type => {
                let (k, type_) = reso.nodes().exactly_one().unwrap();
                assert_eq!(k, NsKind::Type);
                return self.resolve_path_in_type(ctx.node, type_, reso.trailing_path()).map(Some);
            },
        }

        let span = self.hir.path_end_ident(ctx.node).item.ident.span;
        assert!(!reso.is_empty());
        let reso_ctx = self.reso_ctx();
        let (pkg, node) = {
            // Check if we're resolving FnCall's callee.
            let fn_call = if_chain! {
                if reso_ctx == ResoCtx::Value;
                if let Some(fn_call) = self.discover_data.find_fn_call(ctx.node, self.hir);
                then {
                    Some((FnParamsSignature::from_call(fn_call, self.hir), self.hir.node_kind(fn_call).span))
                } else {
                    None
                }
            };
            if let Some((call_sign, call_span)) = fn_call {
                let mut found = None;
                // Function (base) name if there's at least one found.
                let mut name = None;
                // TODO Make this O(1)
                for node in reso.ns_nodes(NsKind::Value) {
                    if let Some(sign) = self.discover_data(node.0)
                        .try_fn_def_signature(node.1)
                    {
                        if name.is_none() {
                            name = Some(self.hir(node.0).fn_def(node.1).name.value.clone());
                        } else {
                            debug_assert_eq!(&self.hir(node.0).fn_def(node.1).name.value, name.as_ref().unwrap());
                        }
                        if &call_sign == sign {
                            found = Some(node);
                            break;
                        }
                    }
                }
                if let Some(found) = found {
                    found
                } else {
                    if let Some(name) = &name {
                        // There are other fns with the same name but none with matching signature.
                        self.error_span(ctx.node, call_span, format!(
                            "couldn't find function `{}`: none of existing functions matches the signature",
                            call_sign.display_with_name(name)));
                        return Err(());
                    }
                    if let Some(node) = reso.ns_nodes(NsKind::Value).next() {
                        // Could be a variable.
                        node
                    } else {
                        let node = reso.ns_nodes(NsKind::Type).next().unwrap();
                        self.error_span(ctx.node, span, format!(
                            "expected function but found {}",
                            self.describe_named(node)));
                        return Err(());
                    }
                }
            } else {
                if reso_ctx == ResoCtx::Import {
                    self.primitive_type(PrimitiveType::Unit);
                    return Ok(None);
                } else {
                    let ns_kind = reso_ctx.to_ns_kind().unwrap();
                    let mut it = reso.ns_nodes(ns_kind);
                    if let Some(node) = it.next() {
                        if let Some(FnDef { name, .. }) = self.hir(node.0).try_fn_def(node.1) {
                            let text = if it.next().is_none() {
                                let sign = self.discover_data(node.0).fn_def_signature(node.1);
                                format!("invalid function reference, must include function's signature: `{}`",
                                    sign.display_with_name(&name.value))
                            } else {
                                "invalid function reference, must include function's signature".into()
                            };
                            self.error_span(ctx.node, span, text);
                            return Err(());
                        } else {
                            assert!(it.next().is_none());
                        }
                        node
                    } else {
                        let node = reso.nodes().next().unwrap().1;
                        let node = self.describe_named(node);
                        let exp_str = match ns_kind {
                            NsKind::Type => "type expression",
                            NsKind::Value => "expression",
                        };
                        self.error_span(ctx.node, span, format!(
                            "expected {}, found {}", exp_str, node));
                        return Err(());
                    }
                }
            }
        };
        self.check_data.insert_path_to_target(ctx.node, (pkg, node));
        Ok(Some(if pkg == self.package_id {
            if let Some(ty) = self.ensure_opt_typing(node)? {
                ty
            } else {
                self.error_span(ctx.node, span, format!(
                    "expected type, found {}", self.describe_named((pkg, node))));
                return Err(());
            }
        } else {
            self.packages[pkg].check_data.typing(node)
        }))
    }

    fn resolve_method_call(&mut self, fn_call: NodeId)
        -> Result<(GlobalNodeId, TypeId), ()>
    {
        let FnCall {
            callee,
            kind,
            params,
        } = self.hir.fn_call(fn_call);
        assert_eq!(*kind, FnCallKind::Method);

        let path = self.hir.path_end_ident(
            self.hir.path_segment(self.hir.path(*callee).segment).suffix[0]);
        let name = &path.item.ident;
        if path.item.ty_args.is_some() {
            todo!();
        }

        let receiver = params[0].value;
        let receiver_ty = self.ensure_typing(receiver)?;

        match self.type_(receiver_ty).data() {
            | TypeData::Struct(_)
            | TypeData::Primitive(_)
            | TypeData::Fn(_)
            => {}
            TypeData::Type(_) => unreachable!(),
            TypeData::UnknownNumber(_) => {
                self.error(receiver, "can't infer type".into());
                return Err(());
            }
        }

        let sign = FnParamsSignature::from_call(fn_call, self.hir);
        if let Some(fn_def) = self.resolve_impl_fn(receiver_ty, &name.value, &sign) {
            self.check_data.insert_path_to_target(*callee, fn_def);
            let fn_ty = self.ensure_typing_global(fn_def)?;
            return Ok((fn_def, fn_ty));
        }
        self.error(*callee, format!(
            "method `{}` not found for type `{}`",
            sign.display_with_name(&name.value),
            self.display_type(receiver_ty)));

        Err(())
    }

    fn resolve_impl_fn(&self, ty: TypeId, name: &Ident, sign: &FnParamsSignature) -> Option<GlobalNodeId> {
        let in_pkg = |
            package_id: PackageId,
            discover_data: &DiscoverData,
            check_data: &CheckData,
        | -> Result<Option<GlobalNodeId>, ()> {
            if let Some(impls) = check_data.impls.get(&ty) {
                assert!(!impls.is_empty());
                if impls.len() > 1 {
                    todo!();
                }
                if let Some(item) = impls[0].values.get(name) {
                    match item {
                        ImplValueItem::Single(_) => return Err(()),
                        ImplValueItem::Fns(fn_defs) => {
                            if let Some(&fn_def) = fn_defs.iter().find(|&&n| discover_data.fn_def_signature(n) == sign) {
                                return Ok(Some((package_id, fn_def)));
                            }
                        }
                    }
                }
            }
            Ok(None)
        };
        match in_pkg(self.package_id, self.discover_data, self.check_data) {
            Ok(Some(v)) => return Some(v),
            Ok(None) => {}
            Err(()) => return None,
        }
        for package in self.packages.iter() {
            match in_pkg(package.id, &package.discover_data, &package.check_data) {
                Ok(Some(v)) => return Some(v),
                Ok(None) => {}
                Err(()) => return None,
            }
        }
        None
    }

    /// Performs type-based path resolution.
    fn resolve_path_in_type(&mut self,
        full_path: NodeId,
        type_: GlobalNodeId,
        path: &[S<Ident>],
    ) -> Result<TypeId, ()> {
        assert!(path.len() > 0);

        let ty = self.ensure_typing_global(type_)?;

        if path.len() == 1 {
            return Ok(ty);
        }

        match self.type_(ty).data() {
            | TypeData::Struct(_)
            | TypeData::Primitive(_)
            | TypeData::Fn(_)
            => {}
            TypeData::Type(_) => unreachable!(),
            TypeData::UnknownNumber(_) => {
                self.error_span(full_path, path[0].span, "can't infer type".into());
                return Err(());
            }
        }

        let item_name = &path[1];

        if_chain! {
            if path.len() == 2;
            if let Some(fn_call) = self.discover_data.find_fn_call(full_path, self.hir);
            then {
                let sign = FnParamsSignature::from_call(fn_call, self.hir);
                if let Some(fn_def) = self.resolve_impl_fn(ty, &item_name.value, &sign) {
                    self.check_data.insert_path_to_target(full_path, fn_def);
                    let fn_ty = self.ensure_typing_global(fn_def)?;
                    return Ok(fn_ty);
                }
                self.error_span(full_path, item_name.span, format!(
                    "associated function `{}` not found for type `{}`",
                    sign.display_with_name(&item_name.value),
                    self.display_type(ty)));
                    return Err(());
            } else {
                self.error_span(full_path, item_name.span, format!(
                    "associated item `{}` not found for type `{}`",
                    item_name.value, self.display_type(ty)));
                    return Err(());
            }
        }
    }

    fn resolve_entry_point(&mut self) -> Result<(), ()> {
        if self.package_kind != PackageKind::Exe {
            return Ok(());
        }
        let node = if let Ok(reso) = self.resolver().resolve_in_package(&["main"]) {
            let node = reso.ns_nodes(NsKind::Value)
                .filter(|n| n.0 == self.package_id)
                .filter(|n| self.discover_data.fn_def_signature(n.1) == &FnParamsSignature::empty())
                .next()
                .map(|n| n.1);
            if let Some(node) = node {
                node
            } else {
                self.error_span(self.hir.root, Span::empty(), format!(
                    "`main::()` function not found in package `{}`", self.package_name));
                return Err(());
            }
        } else {
            return Err(());
        };
        self.check_data.entry_point = Some(node);

        let ty = self.typing(node)?;
        match self.type_(ty).data() {
            TypeData::Fn(FnType { params, result, unsafe_ }) => {
                assert_eq!(params.len(), 0);
                let fn_def = self.hir.fn_def(node);
                if !matches!(self.type_(*result).data(), TypeData::Primitive(PrimitiveType::Unit)) {
                    self.error(fn_def.ret_ty.unwrap(),
                        "`main` function must have unit return type".into());
                }
                if *unsafe_ {
                    self.error_span(node, fn_def.unsafe_.unwrap().span,
                        "`main` function must not be unsafe".into());
                }
                if fn_def.body.is_none() {
                    self.error_span(node, fn_def.name.span,
                        "`main` function must not be external".into());
                }
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn pre_check_impls(&mut self) -> Result<(), ()> {
        for &impl_ in self.discover_data.impls() {
            let _ = self.ensure_typing(impl_);
        }
        Ok(())
    }

    fn resolver(&self) -> Resolver {
        Resolver {
            discover_data: self.discover_data,
            hir: self.hir,
            package_id: self.package_id,
            packages: self.packages,
            diag: self.diag,
            resolve_data: &self.resolve_data,
        }
    }
}

impl HirVisitor for PassImpl<'_> {
    fn before_node(&mut self, ctx: HirVisitorCtx) {
        if let Some(v) = reso_ctx(ctx.link) {
            self.reso_ctxs.push(v);
        }
        if self.has_complete_typing(ctx.node) == Ok(false) {
            let _ = self.do_pre_typing(ctx);
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        let _ = self.check(ctx);
        if self.has_complete_typing(ctx.node) == Ok(false) {
            if let Some(ty) = self.do_typing(ctx).transpose() {
                self.finish_typing(ctx.node, ty);
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
        | Fn(FnLink::TypeParam)
        | Fn(FnLink::RetType)
        | FnDefParamType
        | Impl(ImplLink::For)
        | Impl(ImplLink::TypeParam)
        | Impl(ImplLink::Trait)
        | Let(LetLink::Type)
        | Path(PathLink::EndIdentTyParams)
        | Path(PathLink::SegmentItemTyParams)
        | StructDef(_)
        | StructTypeFieldType
        | StructValue(StructValueLink::Name)
        | TypeAlias(_)
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
