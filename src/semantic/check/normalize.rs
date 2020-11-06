use super::{*, StructType};

#[derive(Default)]
struct Ctx {
    vars: TypeMap<TypeId>,
    depends_on_inference_vars: bool,
}

impl PassImpl<'_> {
    pub fn normalize(&mut self, ty: TypeId) -> TypeId {
        self.normalize0(ty, &mut Ctx::default())
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

        let norm_ty = self.normalize1(ty, ctx);

        if !ctx.depends_on_inference_vars {
            assert!(self.check_data.normalized_types.insert(ty, norm_ty).is_none());
            self.check_data.normalized_types.insert(norm_ty, norm_ty);
        }

        norm_ty
    }

    fn normalize1(&mut self, ty: TypeId, ctx: &mut Ctx) -> TypeId {
        let ty = self.type_(ty);
        let node = ty.node;
        let next = match &ty.data {
            TypeData::Incomplete(_) => unreachable!(),
            TypeData::Instance(TypeInstance {
                ty,
                data,
            }) => {
                match data {
                    TypeInstanceData::Args(args) => {
                        let ty = self.type_(*ty);
                        self.bind_vars(ty.data.type_params(), args, ctx);
                    }
                    TypeInstanceData::Params(_) => {}
                }
                Some(*ty)
            }
            TypeData::Var(kind) => {
                match kind {
                    Var::Inference(_) => {
                        debug_assert!(!ctx.vars.contains_key(&ty.id));
                        assert_eq!(ty.id.0, self.package_id);
                        ctx.depends_on_inference_vars = true;
                        return ty.id;
                    }
                    Var::Param => return ctx.vars.get(&ty.id).copied().unwrap_or(ty.id),
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

    fn normalize_many(&mut self, tys: &mut [TypeId], ctx: &mut Ctx) {
        for ty in tys {
            *ty = self.normalize0(*ty, ctx);
        }
    }

    fn bind_vars(&self, params: &[TypeId], args: &[TypeId], ctx: &mut Ctx) {
        assert_eq!(args.len(), params.len());
        for (&param, &arg) in params.iter().zip(args.iter()) {
            assert_ne!(param, arg);
            assert!(ctx.vars.insert(param, arg).is_none());
        }
    }

    fn normalize_fn(&mut self, mut fn_: FnType, ctx: &mut Ctx) -> FnType {
        let FnType {
            params,
            result,
            unsafe_: _,
        } = &mut fn_;

        self.normalize_many(params, ctx);
        *result = self.normalize0(*result, ctx);

        fn_
    }

    fn normalize_struct(&mut self, mut sty: StructType, ctx: &mut Ctx) -> StructType {
        let StructType {
            base: _,
            fields,
        } = &mut sty;

        for field in fields {
            field.ty = self.normalize0(field.ty, ctx);
        }

        sty
    }
}