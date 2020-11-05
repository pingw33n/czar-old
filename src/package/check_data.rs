use if_chain::if_chain;

use crate::semantic::check::{*, StructType};

use super::*;

#[derive(Clone, Copy)]
pub struct Ctx<'a> {
    pub package_id: PackageId,
    pub check_data: &'a CheckData,
}

impl Ctx<'_> {
    fn check_data<'a>(ctx: Option<Ctx<'a>>, package_id: PackageId, packages: &'a Packages) -> &'a CheckData {
        if_chain! {
            if let Some(ctx) = ctx;
            if package_id == ctx.package_id;
            then {
                ctx.check_data
            } else {
                &packages[package_id].check_data
            }
        }
    }
}

impl Packages {
    pub fn type_(&self, id: TypeId) -> &Type {
        self.type_ctx(id, None)
    }

    pub fn type_ctx<'a>(&'a self, id: TypeId, ctx: Option<Ctx<'a>>) -> &'a Type {
        Ctx::check_data(ctx, id.0, self).type_(id.1)
    }

    pub fn base_type(&self, id: BaseTypeId) -> &BaseType {
        self.base_type_ctx(id, None)
    }

    pub fn base_type_ctx<'a>(&'a self, id: BaseTypeId, ctx: Option<Ctx<'a>>) -> &'a BaseType {
       Ctx::check_data(ctx, id.0, self).base_type(id.1)
    }

    pub fn walk_type_ctx<'a, F, T>(&'a self, mut id: TypeId,
        f: F,
        ctx: Option<Ctx<'a>>,
    ) -> Option<T>
    where F: Fn(&'a Type) -> Option<T>,
    {
        loop {
            let typ = self.type_ctx(id, ctx);
            match &typ.data {
                | TypeData::Base(_)
                | TypeData::Fn(_)
                | TypeData::Incomplete(_)
                | TypeData::Struct(_)
                | TypeData::Var
                => break if let Some(r) = f(typ) {
                    Some(r)
                } else {
                    None
                },
                &TypeData::Instance(TypeInstance { ty, data: _ }) => {
                    if let Some(r) = f(typ) {
                        break Some(r);
                    }
                    id = ty;
                }
            }
        }
    }

    pub fn base_type_of(&self, id: TypeId) -> Option<&BaseType> {
        self.base_type_of_ctx(id, None)
    }

    pub fn base_type_of_ctx<'a>(&'a self, id: TypeId, ctx: Option<Ctx<'a>>) -> Option<&'a BaseType> {
        self.walk_type_ctx(id, |ty| if let &TypeData::Base(v) = &ty.data {
                Some(self.base_type_ctx(v, ctx))
            } else {
                None
            },
            ctx)
    }

    pub fn unwrap_type(&self, ty: TypeId) -> &Type {
        self.unwrap_type_ctx(ty, None)
    }

    pub fn unwrap_type_ctx<'a>(&'a self, ty: TypeId, ctx: Option<Ctx<'a>>) -> &'a Type {
        self.walk_type_ctx(ty, |ty| if matches!(ty.data, TypeData::Instance(_)) {
                None
            } else {
                Some(ty)
            },
            ctx)
            .unwrap()
    }

    pub fn as_lang_item(&self, ty: TypeId) -> Option<LangItem> {
        self.as_lang_item_ctx(ty, None)
    }

    pub fn as_lang_item_ctx(&self, ty: TypeId, ctx: Option<Ctx>) -> Option<LangItem> {
        let ty = self.base_type_of_ctx(ty, ctx)?;
        if ty.package_id.is_std() {
            Ctx::check_data(ctx, PackageId::std(), self).lang().as_item(ty.id())
        } else {
            None
        }
    }

    pub fn as_primitive_ctx(&self, ty: TypeId, ctx: Option<Ctx>) -> Option<PrimitiveType> {
        self.as_lang_item_ctx(ty, ctx)?.into_primitive().ok()
    }

    pub fn as_number_type(&self, ty: TypeId) -> Option<NumberType> {
        self.as_number_type_ctx(ty, None)
    }

    pub fn as_number_type_ctx(&self, ty: TypeId, ctx: Option<Ctx>) -> Option<NumberType> {
        self.as_lang_item_ctx(ty, ctx)?
            .as_number()
    }

    fn unnamed_struct_type_ctx<'a>(&'a self, ty: TypeId, ctx: Option<Ctx<'a>>) -> Option<(TypeId, &'a StructType)> {
        self.walk_type_ctx(ty,|ty| if let TypeData::Struct(v) = &ty.data {
                Some((ty.id, v))
            } else {
                None
            },
            ctx)
    }

    pub fn is_unit_type(&self, ty: TypeId) -> bool {
        self.is_unit_type_ctx(ty, None)
    }

    pub fn is_unit_type_ctx(&self, ty: TypeId, ctx: Option<Ctx>) -> bool {
        self.unnamed_struct_type_ctx(ty, ctx)
            .map(|(_, v)| v.is_unit())
            .unwrap_or(false)
    }
}