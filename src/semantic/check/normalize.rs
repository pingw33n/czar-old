use super::{*, StructType};

const MAX_LEVEL: u32 = u32::max_value();

#[derive(Default)]
struct Ctx {
    vars: TypeMap<(TypeId, u32)>,
    cur_level: u32,
    min_level: u32,
}

impl PassImpl<'_> {
    pub fn normalize(&mut self, ty: TypeId) -> TypeId {
        self.normalize0(ty, &mut Ctx {
            min_level: MAX_LEVEL,
            ..Default::default()
        })
    }

    pub fn normalize_all(&mut self) {
        let types: Vec<_> = self.check_data.types().map(|ty| ty.id).collect();
        for ty in types {
            self.normalize(ty);
        }
    }

    fn normalize0(&mut self, ty: TypeId, ctx: &mut Ctx) -> TypeId {
        if let Some(&ty) = self.check_data.normalized_types.get(&ty) {
            return ty;
        }

        ctx.cur_level += 1;
        let norm_ty = self.normalize1(ty, ctx);
        if ctx.min_level >= ctx.cur_level && !matches!(&self.type_(ty).data,
            TypeData::Ctor(TypeCtor { params, .. }) if !params.is_empty())
        {
            assert!(self.check_data.normalized_types.insert(ty, norm_ty).is_none());
            self.check_data.normalized_types.insert(norm_ty, norm_ty);
        }

        ctx.cur_level -= 1;

        norm_ty
    }

    fn normalize1(&mut self, ty: TypeId, ctx: &mut Ctx) -> TypeId {
        let ty = self.type_(ty);
        let node = ty.node;
        let next = match &ty.data {
            &TypeData::Ctor(TypeCtor {ty, params: _}) => Some(ty),
            TypeData::Incomplete(_) => unreachable!(),
            TypeData::Instance(TypeInstance {ty, args}) => {
                let ty = self.type_(*ty);
                self.bind_vars(ty.data.type_params(), args, ctx);
                Some(ty.id)
            }
            TypeData::Var(kind) => {
                match kind {
                    Var::Inference(_) => {
                        debug_assert!(!ctx.vars.contains_key(&ty.id));
                        assert_eq!(ty.id.0, self.package_id);
                        ctx.min_level = 0;
                        return ty.id;
                    }
                    Var::Param => {
                        if let Some(&(ty, level)) = ctx.vars.get(&ty.id) {
                            ctx.min_level = ctx.min_level.min(level);
                            Some(ty)
                        } else {
                            ctx.min_level = 0;
                            return ty.id;
                        }
                    }
                }
            }
            | TypeData::Fn(_)
            | TypeData::Struct(_)
            => None,
        };
        if let Some(next) = next {
            return self.normalize0(next, ctx);
        }

        let data = match ty.data.clone() {
            TypeData::Fn(v) => {
                TypeData::Fn(self.normalize_fn(v.clone(), ctx))
            }
            TypeData::Struct(v) => {
                TypeData::Struct(self.normalize_struct(v.clone(), ctx))
            }
            | TypeData::Ctor(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            | TypeData::Var(_)
            => unreachable!(),
        };

        match self.type_data_cache.entry(data) {
            hash_map::Entry::Occupied(e) => {
                *e.get()
            }
            hash_map::Entry::Vacant(e) => {
                let ty = self.check_data.insert_type(node, e.key().clone());
                *e.insert(ty)
            }
        }
    }

    fn bind_vars(&self, params: &[TypeId], args: &[TypeId], ctx: &mut Ctx) {
        assert_eq!(args.len(), params.len());
        for (&param, &arg) in params.iter().zip(args.iter()) {
            assert_ne!(param, arg);
            assert!(ctx.vars.insert(param, (arg, ctx.cur_level)).is_none());
        }
    }

    fn normalize_fn(&mut self, mut fn_: FnType, ctx: &mut Ctx) -> FnType {
        let FnType {
            params,
            result,
            unsafe_: _,
        } = &mut fn_;

        for param in params {
            *param = self.normalize0(*param, ctx);
        }
        *result = self.normalize0(*result, ctx);

        fn_
    }

    fn normalize_struct(&mut self, mut sty: StructType, ctx: &mut Ctx) -> StructType {
        let StructType {
            def: _,
            fields,
        } = &mut sty;

        for field in fields {
            field.ty = self.normalize0(field.ty, ctx);
        }

        sty
    }
}