use if_chain::if_chain;

use crate::semantic::check::*;

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

    pub fn base_type_of(&self, id: TypeId) -> Option<&BaseType> {
        self.base_type_of_ctx(id, None)
    }

    pub fn base_type_of_ctx<'a>(&'a self, id: TypeId, ctx: Option<Ctx<'a>>) -> Option<&'a BaseType> {
        self.type_term_ctx(id, ctx).data.base_type()
            .map(|v| self.base_type_ctx(v, ctx))
    }

    pub fn type_term(&self, ty: TypeId) -> &Type {
        self.type_term_ctx(ty, None)
    }

    pub fn type_term_ctx<'a>(&'a self, mut id: TypeId, ctx: Option<Ctx<'a>>) -> &'a Type {
        loop {
            let ty = self.type_ctx(id, ctx);
            match &ty.data {
                | TypeData::Fn(_)
                | TypeData::Incomplete(_)
                | TypeData::Struct(_)
                | TypeData::Var(_)
                => break ty,
                &TypeData::Instance(TypeInstance { ty, data: _ }) => {
                    id = ty;
                }
            }
        }
    }

    pub fn as_lang_item(&self, ty: TypeId) -> Option<LangItem> {
        self.as_lang_item_ctx(ty, None)
    }

    pub fn as_lang_item_ctx(&self, ty: TypeId, ctx: Option<Ctx>) -> Option<LangItem> {
        let bty = self.type_term_ctx(ty, ctx).data.base_type()?;
        if bty.0.is_std() {
            Ctx::check_data(ctx, PackageId::std(), self).lang().as_item(bty)
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

    pub fn is_unit_type(&self, ty: TypeId) -> bool {
        self.is_unit_type_ctx(ty, None)
    }

    pub fn is_unit_type_ctx(&self, ty: TypeId, ctx: Option<Ctx>) -> bool {
        self.type_term_ctx(ty, ctx).data.as_struct().map(|v| v.is_unit()).unwrap_or(false)
    }
}