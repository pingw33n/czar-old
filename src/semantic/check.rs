mod binary_op;
mod data;
mod dump_types;
mod normalize;
mod inference;
mod lang;
mod lex_path;
mod structs;
mod unary_op;

use enum_as_inner::EnumAsInner;
use if_chain::if_chain;
use slab::Slab;
use std::collections::{hash_map, HashMap, HashSet};

use crate::diag::DiagRef;
use crate::hir::{self, *, FieldAccessName};
use crate::hir::traverse::*;
use crate::package::{GlobalNodeId, PackageId, Packages, PackageKind};
use crate::util::iter::IteratorExt;

use super::{*, PathItem};
use discover::{DiscoverData, NsKind};
use resolve::{self, Resolution, ResolutionKind, Resolver, ResolveData};

use inference::{InferenceCtx, InferenceVar};
pub use data::CheckData;
pub use lang::{LangItem, Lang, NumberKind, NumberType, PrimitiveType};
pub use structs::{StructType, StructTypeField};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FnType {
    pub def: Option<GlobalNodeId>,
    pub params: Vec<TypeId>,
    pub result: TypeId,
    pub unsafe_: bool,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LocalTypeId(usize);

pub type TypeId = (PackageId, LocalTypeId);

pub type TypeMap<T> = HashMap<TypeId, T>;
pub type TypeSet = HashSet<TypeId>;

#[derive(Debug)]
pub struct Type {
    pub id: TypeId,
    pub node: GlobalNodeId,
    pub data: TypeData,
}

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, Hash, PartialEq)]
pub enum Var {
    Inference(InferenceVar),
    Param,
}

#[derive(Clone, Debug, EnumAsInner, Eq, Hash, PartialEq)]
pub enum TypeData {
    Ctor(TypeCtor),
    GenericEnv(GenericEnv),
    Fn(FnType),
    Incomplete(IncompleteType),
    Instance(TypeInstance),
    Struct(StructType),
    Var(Var),
}

impl TypeData {
    pub fn def(&self) -> Option<GlobalNodeId> {
        match self {
            Self::Fn(v) => v.def,
            Self::Struct(v) => v.def,
            | Self::Ctor(_)
            | Self::GenericEnv(_)
            | Self::Incomplete(_)
            | Self::Instance(_)
            | Self::Var(_)
            => None,
        }
    }

    pub fn type_params(&self) -> &[TypeId] {
        match self {
            Self::Ctor(TypeCtor { ty: _, params }) => &params[..],
            Self::Incomplete(IncompleteType { params }) => &params[..],
            Self::Instance(TypeInstance { ty: _, args: _ }) => &[],
            | Self::Fn(_)
            | Self::GenericEnv(_)
            | Self::Struct(_)
            | Self::Var(_)
            => &[],
        }
    }

    pub fn as_inference_var(&self) -> Option<InferenceVar> {
        self.as_var()?.as_inference().copied()
    }

    /// Converts `Incomplete` into `Ctor` carrying over the `params`.
    fn finish(&mut self, ty: TypeId) {
        let incomplete = std::mem::replace(self, Self::Ctor(TypeCtor {
            ty,
            params: Vec::new(),
        }));
        let params = incomplete.into_incomplete().unwrap().params;
        *self = Self::Ctor(TypeCtor {
            ty,
            params,
        });
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypeInstance {
    pub ty: TypeId,
    /// Arguments of the instantiated type.
    /// E.g. `String` and `u32` in `HashMap<String, u32>`.
    pub args: Vec<TypeId>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TypeCtor {
    pub ty: TypeId,
    /// Parameters of the type constructor.
    /// E.g. `T` in `type Foo<T> = String`.
    pub params: Vec<TypeId>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct IncompleteType {
    pub params: Vec<TypeId>,
}

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct TypeVarMap {
    entries: Vec<(TypeId, TypeId)>,
}

impl TypeVarMap {
    pub fn insert(&mut self, var: TypeId, val: TypeId) {
        if self.replace(var, val).is_some() {
            panic!("already exists");
        }
    }

    pub fn replace(&mut self, var: TypeId, val: TypeId) -> Option<TypeId> {
        match self.find_idx(var) {
            Ok(i) => Some(std::mem::replace(&mut self.entries[i].1, val)),
            Err(i) => {
                self.entries.insert(i, (var, val));
                None
            }
        }
    }

    pub fn clear(&mut self) {
        self.entries.clear();
    }

    pub fn get(&self, var: TypeId) -> Option<TypeId> {
        self.find_idx(var).ok().map(|i| self.entries[i].1)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(TypeId, TypeId)> + 'a {
        self.entries.iter().copied()
    }

    pub fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item=(TypeId, &'a mut TypeId)> + 'a {
        self.entries.iter_mut().map(|e| (e.0, &mut e.1))
    }

    pub fn vars<'a>(&'a self) -> impl Iterator<Item=TypeId> + 'a {
        self.iter().map(|(v, _)| v)
    }

    pub fn vals<'a>(&'a self) -> impl Iterator<Item=TypeId> + 'a {
        self.iter().map(|(_, v)| v)
    }

    pub fn insert_iter(&mut self, iter: impl Iterator<Item=(TypeId, TypeId)>) {
        for (var, val) in iter {
            self.insert(var, val);
        }
    }

    pub fn replace_iter(&mut self, iter: impl Iterator<Item=(TypeId, TypeId)>) {
        for (var, val) in iter {
            self.replace(var, val);
        }
    }

    fn find_idx(&self, key: TypeId) -> std::result::Result<usize, usize> {
        self.entries.binary_search_by_key(&key, |e| e.0)
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct GenericEnv {
    pub ty: TypeId,
    pub vars: TypeVarMap,
}

#[derive(Debug)]
enum ImplValueItem {
    Single(NodeId),
    Fns(Vec<NodeId /*FnDef*/>),
}

#[derive(Debug)]
struct Impl {
    /// This is instance of type `Foo<T>` in `impl<T> Foo<T>`.
    for_ty: TypeId,
    values: HashMap<Ident, ImplValueItem>,
}

impl CheckData {
    fn finish_type_alias(&mut self, incomplete_ty: LocalTypeId, ty: TypeId) {
        let incomplete_ty = &mut self.type_mut(incomplete_ty).data;
        let old = std::mem::replace(incomplete_ty, TypeData::Ctor(TypeCtor {
            ty,
            params: Vec::new(),
        }));
        let v = incomplete_ty.as_ctor_mut().unwrap();
        v.params = old.into_incomplete().unwrap().params;
    }

    fn finish_named_struct_type(&mut self,
        node: NodeId,
        incomplete_ty: LocalTypeId,
        struct_ty: LocalTypeId,
    ) {
        // Set StructType::def
        let pkg = self.package_id;
        let structd = self.type_mut(struct_ty).data.as_struct_mut().unwrap();
        structd.def = Some((pkg, node));

        self.type_mut(incomplete_ty).data.finish((pkg, struct_ty));
    }
}

pub type Result<T> = std::result::Result<T, ()>;

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
    pub fn run(self) -> Result<CheckData> {
        let mut check_data = CheckData::new(self.package_id);

        let imp = &mut PassImpl {
            discover_data: self.discover_data,
            check_data: &mut check_data,
            package_id: self.package_id,
            package_name: self.package_name,
            package_kind: self.package_kind,
            packages: self.packages,
            reso_ctxs: Default::default(),
            hir: self.hir,
            diag: self.diag,
            typing_state: Default::default(),
            resolve_data: self.resolve_data,
            inference_ctxs: Vec::new(),
            type_data_ids: Default::default(),
        };
        if self.package_id.is_std() {
            imp.make_lang()?;
        }

        let _ = imp.pre_check_impls();

        self.hir.traverse(imp);

        // println!();
        // imp.dump_all_types();

        for ty in imp.check_data.types() {
            assert_eq!(ty.id.0, self.package_id);
        }

        if cfg!(debug_assertions) {
            let failed: Vec<_> = imp.typing_state.iter()
                .filter(|&(_, &s)| s == TypingState::Failed)
                .map(|(&n, _)| n)
                .collect();
            if !failed.is_empty() {
                let diag_empty = self.diag.borrow().reports().is_empty();
                if diag_empty {
                    dbg!(self.package_id);
                    for node in failed {
                        dbg!(self.hir.node_kind(node));
                    }
                }
                assert!(!diag_empty, "{:?}", self.package_id);
            }
        }
        imp.check_entry_point()?;
        if self.diag.borrow().error_count() > 0 {
            return Err(());
        }

        // println!();
        // imp.dump_all_types();

        imp.normalize_all();

        for ty in imp.check_data.types() {
            assert!(ty.data.as_incomplete().is_none(), "{:?} {:?}", ty, imp.hir(ty.node.0).node_kind(ty.node.1));
        }

        // println!();
        // imp.dump_all_types();

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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypingState {
    Incomplete,
    Failed,
}

struct PassImpl<'a> {
    discover_data: &'a DiscoverData,
    check_data: &'a mut CheckData,
    package_id: PackageId,
    package_name: &'a Ident,
    package_kind: PackageKind,
    packages: &'a Packages,
    reso_ctxs: Vec<ResoCtx>,
    hir: &'a Hir,
    diag: DiagRef<'a>,
    typing_state: NodeMap<TypingState>,
    resolve_data: &'a ResolveData,
    inference_ctxs: Vec<InferenceCtx>,
    type_data_ids: HashMap<TypeData, TypeId>,
}

impl PassImpl<'_> {
    fn typing_state(&self, node: NodeId) -> Option<TypingState> {
        self.typing_state.get(&node).copied()
    }

    fn ensure_opt_typing(&mut self, node: NodeId) -> Result<Option<TypeId>> {
        if self.typing_state(node) == Some(TypingState::Failed) {
            return Err(());
        }
        let ty = if let Some(ty) = self.check_data.try_typing(node) {
            ty
        } else {
            self.hir.traverse_from(node, self);
            if self.typing_state(node) == Some(TypingState::Failed) {
                return Err(());
            }
            if let Some(ty) = self.check_data.try_typing(node) {
                ty
            } else {
                return Ok(None);
            }
        };
        Ok(Some(self.type_(ty).id))
    }

    fn ensure_typing(&mut self, node: NodeId) -> Result<TypeId> {
        self.ensure_opt_typing(node).transpose().unwrap()
    }

    fn ensure_typing_global(&mut self, node: GlobalNodeId) -> Result<TypeId> {
        let r = if node.0 == self.package_id {
            self.ensure_typing(node.1)?
        } else {
            self.packages[node.0].check_data.typing(node.1)
        };
        Ok(r)
    }

    fn ensure_typing_many(&mut self, nodes: &[NodeId]) -> Result<Vec<TypeId>> {
        let mut r = Vec::with_capacity(nodes.len());
        let mut err = false;
        for &node in nodes {
            if let Ok(ty) = self.ensure_typing(node) {
                r.push(ty);
            } else {
                err = true;
            }
        }
        if err {
            Err(())
        } else {
            Ok(r)
        }
    }

    fn check_data(&self, package_id: PackageId) -> &CheckData {
        if package_id == self.package_id {
            &self.check_data
        } else {
            &self.packages[package_id].check_data
        }
    }

    fn cdctx(&self) -> Option<crate::package::check_data::Ctx> {
        Some(crate::package::check_data::Ctx {
            package_id: self.package_id,
            check_data: self.check_data,
        })
    }

    fn type_(&self, id: TypeId) -> &Type {
        self.packages.type_ctx(id, self.cdctx())
    }

    fn underlying_type(&self, ty: TypeId) -> &Type {
        self.packages.underlying_type_ctx(ty, self.cdctx())
    }

    fn type_param(&self, ty: TypeId) -> Option<&Type> {
        let ty = self.underlying_type(ty);
        if matches!(ty.data, TypeData::Var(Var::Param)) {
            Some(ty)
        } else {
            None
        }
    }

    fn insert_type(&mut self, node: GlobalNodeId, data: TypeData) -> TypeId {
        self.check_data.insert_type(node, data)
    }

    fn insert_typing(&mut self, node: NodeId, data: TypeData) -> TypeId {
        debug_assert_ne!(self.typing_state(node), Some(TypingState::Failed));
        let ty = self.insert_type((self.package_id, node), data);
        self.check_data.insert_typing(node, ty);
        ty
    }

    fn typing(&self, node: NodeId) -> Result<TypeId> {
        if self.typing_state(node) == Some(TypingState::Failed) {
            return Err(());
        }
        Ok(self.check_data.typing(node))
    }

    fn typing_global(&self, node: GlobalNodeId) -> Result<TypeId> {
        if node.0 == self.package_id {
            self.typing(node.1)
        } else {
            Ok(self.check_data(node.0).typing(node.1))
        }
    }

    fn begin_typing(&mut self, node: NodeId, params: Vec<TypeId>) -> TypeId {
        let ty = self.insert_type((self.package_id, node), TypeData::Incomplete(IncompleteType {
            params,
        }));
        self.check_data.insert_typing(node, ty);
        assert!(self.typing_state.insert(node, TypingState::Incomplete).is_none());
        ty
    }

    fn insert_failed_typing(&mut self, node: NodeId) {
        assert!(!self.diag.borrow().reports().is_empty());
        assert!(matches!(self.typing_state.insert(node, TypingState::Failed),
            None | Some(TypingState::Incomplete)));
    }

    fn finish_typing(&mut self, node: NodeId, ty: Result<TypeId>) {
        assert!(matches!(self.typing_state.remove(&node), None | Some(TypingState::Incomplete)));
        let ty = match ty {
            Ok(ty) => ty,
            Err(()) => {
                self.insert_failed_typing(node);
                return;
            }
        };
        if let Some(incomplete_ty) = self.check_data.try_typing(node) {
            assert_eq!(incomplete_ty.0, self.package_id);
            debug_assert_eq!(self.check_data.type_(incomplete_ty.1).node, (self.package_id, node));
            match self.hir.node_kind(node).value {
                NodeKind::Struct => {
                    assert_eq!(ty.0, self.package_id);
                    self.check_data.finish_named_struct_type(node, incomplete_ty.1, ty.1);
                }
                NodeKind::TypeAlias => {
                    self.check_data.finish_type_alias(incomplete_ty.1, ty);
                }
                _ => unreachable!(),
            }
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

    fn normalized_lang_type(&mut self, lang_item: LangItem) -> TypeId {
        let ty = self.std().type_(lang_item);
        self.normalize(ty)
    }

    fn do_pre_typing(&mut self, ctx: HirVisitorCtx) -> Result<()> {
        match ctx.kind {
            NodeKind::FnDef => {
                let FnDef {
                    name,
                    vis: _,
                    ty_params,
                    params,
                    ret_ty,
                    unsafe_,
                    variadic: _,
                    body,
                } = self.hir.fn_def(ctx.node);
                if body.is_none() && unsafe_.is_none() {
                    self.error_span(ctx.node, name.span,
                        "external function must be marked as `unsafe`".into());
                }
                let params = self.ensure_typing_many(params);
                let result = if let Some(n) = *ret_ty {
                    self.ensure_typing(n)
                } else {
                    Ok(self.std().unit_type())
                };

                let ty_params = self.ensure_typing_many(ty_params);

                let ty = self.check_data.insert_type((self.package_id, ctx.node),
                    TypeData::Fn(FnType {
                        def: Some((self.package_id, ctx.node)),
                        params: params?,
                        result: result?,
                        unsafe_: unsafe_.is_some(),
                    }));

                let ty_params = ty_params?;
                self.insert_typing(ctx.node, TypeData::Ctor(TypeCtor {
                    ty,
                    params: ty_params,
                }));
            }
            NodeKind::Impl => {
                let unit_ty = self.std().unit_type();
                self.check_data.insert_typing(ctx.node, unit_ty);

                let hir::Impl {
                    ty_params,
                    trait_,
                    for_,
                    items,
                } = self.hir.impl_(ctx.node);
                if trait_.is_some() {
                    todo!();
                }

                let mut err = self.ensure_typing_many(ty_params).is_err();

                self.reso_ctxs.push(ResoCtx::Type);
                let for_ty = self.ensure_typing(*for_);
                assert_eq!(self.reso_ctxs.pop().unwrap(), ResoCtx::Type);
                let for_ty = for_ty?;
                let for_ty = self.type_(for_ty).data.as_ctor().unwrap().ty;

                let def = if let Some(def) = self.underlying_type(for_ty).data.def() {
                    if def.0 != self.package_id {
                        self.error(*for_,
                            "cannot define inherent `impl` for a type from outside of this package".into());
                        err = true;
                    }
                    def
                } else {
                    self.error(*for_,
                        "can't define inherent `impl` on a type parameter".into());
                    return Err(());
                };

                let mut dup_items = Vec::new();
                let impls = self.check_data.impls.entry(def)
                    .or_insert_with(Vec::new);
                let mut impl_values = HashMap::with_capacity(items.len());
                for &item in items {
                    match self.hir.node_kind(item).value {
                        NodeKind::FnDef => {
                            let name = &self.hir.fn_def(item).name;
                            let sign = self.discover_data.fn_def_signature(item);
                            let mut dup = false;
                            for impl_ in &*impls {
                                match impl_.values.get(&name.value) {
                                    Some(ImplValueItem::Single(_)) => {
                                        dup = true;
                                        break;
                                    }
                                    Some(ImplValueItem::Fns(fns)) => {
                                        debug_assert!(!fns.iter().any(|&n| n == item));
                                        let discover_data = self.discover_data;
                                        if fns.iter().any(|&n| discover_data.fn_def_signature(n) == sign) {
                                            dup = true;
                                            break;
                                        }
                                    }
                                    None => {}
                                }
                            }

                            if !dup {
                                match impl_values.entry(name.value.clone()) {
                                    hash_map::Entry::Occupied(mut e) => {
                                        match e.get_mut() {
                                            ImplValueItem::Single(_) => {
                                                dup = true;
                                            }
                                            ImplValueItem::Fns(fns) => {
                                                debug_assert!(!fns.iter().any(|&n| n == item));
                                                let discover_data = self.discover_data;
                                                if fns.iter().any(|&n| discover_data.fn_def_signature(n) == sign) {
                                                    dup = true;
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
                            if dup {
                                err = true;
                                dup_items.push(item);
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                impls.push(Impl {
                    for_ty,
                    values: impl_values,
                });
                for item in dup_items {
                    let name = &self.hir.fn_def(item).name;
                    let sign = self.discover_data.fn_def_signature(item);
                    self.error_span(item, name.span, format!(
                        "function `{}` is defined multiple times across inherent `impl`s",
                        sign.display_with_name(&name.value)));
                }
                if err {
                    return Err(());
                }
            }
            NodeKind::Struct => {
                let Struct { ty_params, .. } = self.hir.struct_(ctx.node);
                let ty_params = self.ensure_typing_many(ty_params)?;
                self.begin_typing(ctx.node, ty_params);
            }
            NodeKind::TypeAlias => {
                let TypeAlias { vis: _, name: _, ty_params, ty: _ } = self.hir.type_alias(ctx.node);
                let ty_params = self.ensure_typing_many(ty_params)?;
                self.begin_typing(ctx.node, ty_params);
            }
            NodeKind::TypeParam => {
                self.insert_typing(ctx.node, TypeData::Var(Var::Param));
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
            | NodeKind::StructLiteral
            | NodeKind::StructLiteralField
            | NodeKind::StructType
            | NodeKind::TyExpr
            | NodeKind::Use
            | NodeKind::While
            => {},
            | NodeKind::BlockFlowCtl
            | NodeKind::Cast
            | NodeKind::Loop
            | NodeKind::Range
            | NodeKind::SliceLiteral
            => todo!("{:?}", self.hir.node_kind(ctx.node)),
        }
        Ok(())
    }

    fn check(&mut self, ctx: HirVisitorCtx) -> Result<()> {
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
                    self.std().unit_type()
                };
                if let Some(body) = *body {
                    let actual_ret_ty = self.typing(body)?;
                    self.unify(actual_ret_ty, expected_ret_ty);
                    if self.normalize(actual_ret_ty) != self.normalize(expected_ret_ty) {
                        let node = self.hir.block(body).exprs.last()
                            .copied().unwrap_or(body);
                        self.error(node, format!(
                            "mismatching return types: function `{fname}::{fsign}` expects `{exp}`, found `{act}`",
                            fname=name.value, fsign= FnParamsSignature::from_def(ctx.node, self.hir),
                            exp=self.display_type(expected_ret_ty),
                            act=self.display_type(actual_ret_ty)));
                    }
                }
            },
            _ => {},
        }
        Ok(())
    }

    fn do_typing(&mut self, ctx: HirVisitorCtx) -> Result<Option<TypeId>> {
        let ty = match ctx.kind {
            NodeKind::Block => {
                if let Some(&expr) = self.hir.block(ctx.node).exprs.last() {
                    if self.hir.node_kind(expr).value.is_def() {
                        self.std().unit_type()
                    } else {
                        self.typing(expr)?
                    }
                } else {
                    self.std().unit_type()
                }
            }
            NodeKind::FieldAccess => {
                self.check_data.set_lvalue(ctx.node);
                let hir::FieldAccess { receiver, name: field } = self.hir.field_access(ctx.node);
                let struct_ty = self.typing(*receiver)?;
                self.resolve_struct_field(struct_ty, ctx.node, field)?
            }
            NodeKind::FnCall => self.check_fn_call(&ctx)?,
            NodeKind::FnDef => return Err(()),
            NodeKind::FnDefParam => {
                self.check_data.set_lvalue(ctx.node);
                self.typing(self.hir.fn_def_param(ctx.node).ty)?
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = self.hir.if_expr(ctx.node);
                if let Ok(actual_cond_ty) = self.typing(cond) {
                    if self.normalize(actual_cond_ty) != self.normalized_lang_type(LangItem::Primitive(PrimitiveType::Bool)) {
                        self.error(cond, format!(
                            "invalid type of `if` condition: expected `bool`, found `{}`",
                            self.display_type(actual_cond_ty)));
                    }
                }
                let if_true_ty = self.typing(if_true)?;
                if let Some(if_false) = if_false {
                    let if_false_ty = self.typing(if_false)?;
                    self.unify(if_true_ty, if_false_ty);
                    if self.normalize(if_true_ty) != self.normalize(if_false_ty) {
                        self.error(ctx.node, format!("mismatching types of `if` arms: `{}`, `{}`",
                            self.display_type(if_true_ty),
                            self.display_type(if_false_ty)));
                    }
                }
                if_true_ty
            }
            NodeKind::Impl => unreachable!(),
            NodeKind::Let => {
                self.std().type_(LangItem::Primitive(PrimitiveType::Bool))
            }
            NodeKind::LetDef => {
                self.check_data.set_lvalue(ctx.node);
                let &LetDef { ty, init, .. } = self.hir.let_def(ctx.node);
                if let Some(ty) = ty {
                    let ty = self.typing(ty)?;
                    if let Some(init) = init {
                        let init_ty = self.typing(init)?;
                        self.unify(ty, init_ty);
                        if self.normalize(init_ty) != self.normalize(ty) {
                            self.error(init, format!("mismatching types: expected `{}`, found `{}`",
                                self.display_type(ty), self.display_type(init_ty)));
                        }
                    }
                    ty
                } else if let Some(init) = init {
                    self.typing(init)?
                } else {
                    self.error(ctx.node, "can't infer variable type".into());
                    return Err(());
                }
            }
            NodeKind::Literal => {
                match self.hir.literal(ctx.node) {
                    &Literal::Bool(_) => self.std().type_(LangItem::Primitive(PrimitiveType::Bool)),
                    &Literal::Int(IntLiteral { ty, .. }) => {
                        if let Some(ty) = ty {
                            use IntTypeSuffix::*;
                            self.std().type_(LangItem::Primitive(match ty {
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
                            }))
                        } else {
                            self.new_inference_var(ctx.node, InferenceVar::Number(NumberKind::Int))
                        }
                    },
                    &Literal::Float(FloatLiteral { ty, .. }) => {
                        if let Some(ty) = ty {
                            use FloatTypeSuffix::*;
                            self.std().type_(LangItem::Primitive(match ty {
                                F32 => PrimitiveType::F32,
                                F64 => PrimitiveType::F64,
                            }))
                        } else {
                            self.new_inference_var(ctx.node, InferenceVar::Number(NumberKind::Float))
                        }
                    }
                    Literal::Unit => self.std().unit_type(),
                    Literal::String(_) => self.std().type_(LangItem::String),
                    Literal::Char(_) => self.std().type_(LangItem::Primitive(PrimitiveType::Char)),
                }
            }
            NodeKind::Module => return Ok(None),
            NodeKind::Op => {
                match self.hir.op(ctx.node) {
                    &Op::Binary(op) => self.check_binary_op(op, ctx.node)?,
                    &Op::Unary(op) => self.check_unary_op(op, ctx.node)?,
                }
            }
            NodeKind::Path => return self.check_path_start(ctx.node),
            | NodeKind::PathEndEmpty
            | NodeKind::PathEndStar
            => return self.check_path(ctx.node),
            NodeKind::PathEndIdent => {
                return if self.discover_data.find_method_call(ctx.node, self.hir).is_none() {
                    self.check_path(ctx.node)
                } else {
                    Ok(None)
                };
            },
            NodeKind::PathSegment => return self.check_path_segment(ctx.node),
            NodeKind::Struct => {
                self.typing(self.hir.struct_(ctx.node).ty)?
            }
            NodeKind::StructType => self.check_struct_type(ctx.node)?,
            NodeKind::StructLiteralField => {
                let value = self.hir.struct_literal_field(ctx.node).value;
                self.typing(value)?
            }
            NodeKind::StructLiteral => self.check_struct_literal(ctx.node)?,
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
                let hir::TypeAlias { vis: _, name: _, ty_params: _, ty } = self.hir.type_alias(ctx.node);
                self.typing(*ty)?
            }
            NodeKind::Use => self.std().unit_type(),
            NodeKind::While
            => {
                let cond = self.hir.while_(ctx.node).cond;
                if let Ok(actual_cond_ty) = self.typing(cond) {
                    if self.normalize(actual_cond_ty) != self.normalized_lang_type(LangItem::Primitive(PrimitiveType::Bool)) {
                        self.error(cond, format!(
                            "invalid type of `while` condition: expected `bool`, found `{}`",
                            self.display_type(actual_cond_ty)));
                    }
                }
                self.std().unit_type()
            },
            _ => unimplemented!("{:?}", self.hir.node_kind(ctx.node))
        };
        Ok(Some(ty))
    }

    fn path_ty_args(path: &[PathItem]) -> Option<S<&[NodeId]>> {
        let mut r = None;
        for path_item in path {
            if let Some(args) = &path_item.ty_args {
                assert!(r.replace(args.span.spanned(&args.value[..])).is_none());
            }
        }
        r
    }

    fn has_complete_typing(&self, node: NodeId) -> Result<bool> {
        match self.typing_state(node) {
            Some(TypingState::Incomplete) => return Ok(false),
            Some(TypingState::Failed) => return Err(()),
            None => {}
        }
        let id = if let Some(v) = self.check_data.try_typing(node) {
            v
        } else {
            return Ok(false);
        };
        debug_assert!(self.type_(id).data.as_incomplete().is_none());
        Ok(true)
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
        match &ty.data {
            TypeData::Fn(FnType { def: _, params, result, unsafe_ }) => {
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
                if !self.is_unit_type(*result) {
                    write!(f, " -> ")?;
                    self.display_type0(*result, f)?;
                }
                Ok(())
            }
            TypeData::Struct(sty) => self.display_struct_type(sty, f),
            &TypeData::Var(var) => {
                match var {
                    Var::Inference(ivar) => {
                        match ivar {
                            InferenceVar::Any => write!(f, "<?T'{}>", (ty.id.1).0),
                            InferenceVar::Number(n) => match n {
                                NumberKind::Float => write!(f, "<float>"),
                                NumberKind::Int => write!(f, "<integer>"),
                            }
                        }
                    }
                    Var::Param => {
                        let name = &self.hir(ty.node.0).type_param(ty.node.1).name.value;
                        write!(f, "{}", name)
                    }
                }
            }
            TypeData::Incomplete(_) => write!(f, "<incomplete>"),
            | &TypeData::Ctor(TypeCtor { ty, params: _ })
            | &TypeData::Instance(TypeInstance { ty, args: _ })
            | &TypeData::GenericEnv(GenericEnv { ty, vars: _ })
            => self.display_type0(ty, f),
        }
    }

    fn display_struct_type(&self, ty: &StructType, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if let Some(def) = ty.def {
            let name = &self.hir(def.0).struct_(def.1).name.value;
            write!(f, "{}", name)
        } else {
            let StructType { def: _, fields } = ty;
            write!(f, "{{")?;
            for (i, StructTypeField { name, ty }) in fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                if let FieldAccessName::Ident(name) = name {
                    write!(f, "{}: ", name)?;
                }
                self.display_type0(*ty, f)?;
            }
            if ty.is_tuple() && fields.len() == 1 {
                write!(f, ",")?;
            }
            write!(f, "}}")
        }
    }

    fn check_fn_call(&mut self, ctx: &HirVisitorCtx) -> Result<TypeId> {
        let FnCall {
            callee,
            kind,
            args,
        } = self.hir.fn_call(ctx.node);
        let (fn_def_node, fn_ty) = match *kind {
            FnCallKind::Free => {
                let callee_ty = self.typing(*callee)?;
                let callee_ty = self.normalize(callee_ty);
                let fn_def = if let Some(FnType { def, .. }) = self.underlying_type(callee_ty).data.as_fn() {
                    if def.is_none() {
                        todo!()
                    }
                    def.unwrap()
                } else {
                    self.error(*callee, format!(
                        "invalid callee type: expected function, found `{}`",
                        self.display_type(callee_ty)));
                    return Err(());
                };
                (fn_def, callee_ty)
            }
            FnCallKind::Method => {
                self.check_method_call(ctx.node)?
            }
        };

        let fn_ty = self.normalize(fn_ty);
        let params = self.underlying_type(fn_ty).data.as_fn().unwrap().params.clone();
        assert_eq!(args.len(), params.len());

        for (arg, &param_ty) in args
            .iter()
            .zip(params.iter())
        {
            let arg_ty = if let Ok(ty) = self.typing(arg.value) {
                ty
            } else {
                continue;
            };
            self.unify(arg_ty, param_ty);
            if self.normalize(arg_ty) != self.normalize(param_ty) {
                let hir = self.hir(fn_def_node.0);
                let name = &hir.fn_def(fn_def_node.1).name.value;
                self.error(arg.value, format!(
                    "mismatching types in fn call of `{f}`: expected `{param}`, found `{arg}`",
                    f=FnParamsSignature::from_def(fn_def_node.1, hir).display_with_name(name),
                    param=self.display_type(param_ty), arg=self.display_type(arg_ty)));
            }
        }

        let res_ty = self.underlying_type(fn_ty).data.as_fn().unwrap().result;

        Ok(res_ty)
    }

    fn describe_named(&self, node: GlobalNodeId) -> String {
        let hir = self.hir(node.0);
        let kind = hir.node_kind(node.1).value;
        if kind == NodeKind::Struct {
            let prim = self.typing_global(node).ok()
                .and_then(|ty| self.as_primitive(ty))
                .is_some();
            if prim {
                let name = self.discover_data(node.0).name(node.1, hir).unwrap();
                return format!("primitive type `{}`", name.value);
            }
        }
        self.discover_data(node.0).describe_named(node.1, hir).unwrap()
    }

    fn check_method_call(&mut self, fn_call: NodeId) -> Result<(GlobalNodeId, TypeId)> {
        let fnc = self.hir.fn_call(fn_call);
        assert_eq!(fnc.kind, FnCallKind::Method);

        let (path_end_node, path_end_item) = fnc.callee_path_item(self.hir);
        let name = &path_end_item.ident;

        let receiver = fnc.args[0].value;
        let receiver_ty = self.ensure_typing(receiver)?;

        if self.underlying_type(receiver_ty).data.as_inference_var().is_some() {
            self.error(receiver, "can't infer type".into());
            return Err(());
        }

        let fn_name = PathItem::from_hir(path_end_node, path_end_item);
        let sign = FnParamsSignature::from_call(fn_call, self.hir);
        if let Some((fn_def, fn_ty)) = self.check_impl_fn(receiver_ty, fn_name, &sign)? {
            self.check_data.insert_path_to_target(fnc.callee, fn_def);
            self.check_data.insert_typing(fnc.callee, fn_ty);

            Ok((fn_def, fn_ty))
        } else {
            self.error(fnc.callee, format!(
                "method `{}` not found for type `{}`",
                sign.display_with_name(&name.value),
                self.display_type(receiver_ty)));
            Err(())
        }
    }

    fn check_impl_fn(&mut self,
        ty: TypeId,
        name: PathItem,
        sign: &FnParamsSignature,
    ) -> Result<Option<(GlobalNodeId, TypeId)>> {
        let in_pkg = |
            package_id: PackageId,
            discover_data: &DiscoverData,
            check_data: &CheckData,
        | -> Result<Option<(GlobalNodeId, TypeId)>> {
            let def = if let Some(v) = self.underlying_type(ty).data.def() {
                v
            } else {
                return Ok(None)
            };
            if let Some(impls) = check_data.impls.get(&def) {
                assert!(!impls.is_empty());
                for impl_ in impls {
                    if let Some(item) = impl_.values.get(&name.name.value) {
                        match item {
                            ImplValueItem::Single(_) => return Err(()),
                            ImplValueItem::Fns(fn_defs) => {
                                if let Some(&fn_def) = fn_defs.iter().find(|&&n| discover_data.fn_def_signature(n) == sign) {
                                    return Ok(Some(((package_id, fn_def), impl_.for_ty)));
                                }
                            }
                        }
                    }
                }
            }
            Ok(None)
        };
        let (fn_def, for_ty) = 'outer: loop {
            match in_pkg(self.package_id, self.discover_data, self.check_data) {
                Ok(Some(v)) => break 'outer v,
                Ok(None) => {}
                Err(()) => return Ok(None),
            }
            for package in self.packages.iter() {
                match in_pkg(package.id, &package.discover_data, &package.check_data) {
                    Ok(Some(v)) => break 'outer v,
                    Ok(None) => {}
                    Err(()) => return Ok(None),
                }
            }
            return Ok(None);
        };

        let fn_ty = self.ensure_typing_global(fn_def)?;
        let fn_ty = self.check_path_ty_args(&[name], fn_ty, true)?;
        let fn_ty = self.normalize(fn_ty);

        let for_ty = self.normalize(for_ty);
        let mut genv_vars = TypeVarMap::default();
        let ty = self.normalize(ty);
        let ty_genv_vars = &self.type_(ty).data.as_generic_env().unwrap().vars;
        for (var, val) in self.type_(for_ty).data.as_generic_env().unwrap().vars.iter() {
            let from_var = self.type_param(val).unwrap().id;
            let var = ty_genv_vars.get(var).unwrap();
            genv_vars.insert(from_var, var);
        }

        let fn_ty_node = self.type_(fn_ty).node;
        let fn_ty = self.check_data.insert_type(fn_ty_node, TypeData::Ctor(TypeCtor {
            ty: fn_ty,
            params: genv_vars.vars().collect(),
        }));
        let fn_ty = self.check_data.insert_type(fn_ty_node, TypeData::Instance(TypeInstance {
            ty: fn_ty,
            args: genv_vars.vals().collect(),
        }));

        Ok(Some((fn_def, fn_ty)))
    }

    /// Performs type-based path resolution and checking.
    fn check_type_path(&mut self,
        full_path: NodeId /*PathEndIdent*/,
        type_: GlobalNodeId,
        path: &[PathItem],
    ) -> Result<TypeId> {
        assert!(path.len() > 1);

        let ty = self.ensure_typing_global(type_)?;

        debug_assert!(self.type_(ty).data.as_inference_var().is_none());

        let mut err = false;
        let ty = self.check_path_ty_args(&path[..1], ty, true)
            .unwrap_or_else(|_| {
                err = true;
                ty
            });
        let ty = self.normalize(ty);

        let item_name = &path[1].name;

        let r = if_chain! {
            if path.len() == 2;
            if let Some(fn_call) = self.discover_data.find_fn_call(full_path, self.hir);
            then {
                let sign = FnParamsSignature::from_call(fn_call, self.hir);
                if let Some((fn_def, fn_ty)) = self.check_impl_fn(ty, path[1].clone(), &sign)? {
                    self.check_data.insert_path_to_target(full_path, fn_def);
                    Ok(fn_ty)
                } else {
                    self.error_span(full_path, item_name.span, format!(
                        "associated function `{}` not found for type `{}`",
                        sign.display_with_name(&item_name.value),
                        self.display_type(ty)));
                    Err(())
                }
            } else {
                self.error_span(full_path, item_name.span, format!(
                    "associated item `{}` not found for type `{}`",
                    item_name.value, self.display_type(ty)));
                Err(())
            }
        };
        if err {
            Err(())
        } else {
            r
        }
    }

    fn check_entry_point(&mut self) -> Result<()> {
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

        let ty = self.typing(node)?;
        let fn_ = self.underlying_type(ty).data.as_fn().unwrap();
        assert_eq!(fn_.params.len(), 0);
        let fn_def = self.hir.fn_def(node);
        let mut err = false;
        if !self.is_unit_type(fn_.result) {
            self.error(fn_def.ret_ty.unwrap(),
                "`main` function must have unit return type".into());
            err = true;
        }
        if fn_.unsafe_ {
            self.error_span(node, fn_def.unsafe_.unwrap().span,
                "`main` function must not be unsafe".into());
            err = true;
        }
        if fn_def.body.is_none() {
            self.error_span(node, fn_def.name.span,
                "`main` function must not be external".into());
            err = true;
        }
        if !fn_def.ty_params.is_empty() {
            self.error_span(node, fn_def.name.span,
                "`main` function must not have type parameters".into());
            err = true;
        }
        if err {
            Err(())
        } else {
            let ty = self.insert_type((self.package_id, node), TypeData::Instance(TypeInstance {
                ty: self.typing(node)?,
                args: Vec::new(),
            }));
            self.check_data.entry_point = Some(self.normalize(ty));
            Ok(())
        }
    }

    fn pre_check_impls(&mut self) -> Result<()> {
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
        if ctx.kind == NodeKind::FnDef {
            self.begin_inference();
        }

        if self.has_complete_typing(ctx.node) == Ok(false) {
            if self.do_pre_typing(ctx).is_err() {
                self.insert_failed_typing(ctx.node);
            }
        }
    }

    fn after_node(&mut self, ctx: HirVisitorCtx) {
        let _ = self.check(ctx);
        if self.has_complete_typing(ctx.node) == Ok(false) {
            if let Some(ty) = self.do_typing(ctx).transpose() {
                self.finish_typing(ctx.node, ty);
            }
        }

        if ctx.kind == NodeKind::FnDef {
            self.finish_inference();
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
        | SliceLiteral(_)
        | StructLiteral(StructLiteralLink::Field)
        | StructLiteral(StructLiteralLink::FieldValue)
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
        | StructLiteral(StructLiteralLink::Name)
        | StructTypeFieldType
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
