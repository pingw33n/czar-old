use super::{*, StructType};

#[derive(Clone)]
pub struct NormalizedType {
    pub ty: TypeId,
    /// Var values that were used to instantiate the type.
    pub vars: TypeMap<TypeId>,
}

#[derive(Default)]
struct Ctx {
    vars: TypeMap<TypeId>,
    depends_on_inference_var: bool,
}

impl PassImpl<'_> {
    pub fn normalize(&mut self, ty: TypeId) -> TypeId {
        if let Some(nty) = self.check_data.normalized_types.get(&ty) {
            return nty.ty;
        }
        let ctx = &mut Ctx::default();
        let norm_ty = self.normalize0(ty, ctx);
        if !ctx.depends_on_inference_var {
            let vars: HashMap<_, _> = ctx.vars.iter()
                // Remove intermediate var bindings.
                .filter(|(_, &ty)| {
                    let ty = self.type_term(ty);
                    if matches!(ty.data, TypeData::Var(_)) {
                        !ctx.vars.contains_key(&ty.id)
                    } else {
                        true
                    }
                })
                .map(|(&k, &v)| (k, v))
                .collect();
            let nty = NormalizedType {
                ty: norm_ty,
                vars,
            };
            assert!(self.check_data.normalized_types.insert(ty, nty.clone()).is_none());
            self.check_data.normalized_types.insert(norm_ty, nty);
        }
        norm_ty
    }

    pub fn normalize_all(&mut self) {
        let types: Vec<_> = self.check_data.typings.values().copied().collect();
        for ty in types {
            self.normalize(ty);
        }

        let mut vars = Vec::new();
        for nty in self.check_data.normalized_types.values() {
            vars.extend(nty.vars.values().copied());
        }
        for ty in vars {
            self.normalize(ty);
        }
    }

    fn normalize0(&mut self, ty: TypeId, ctx: &mut Ctx) -> TypeId {
        let ty = self.type_(ty);
        let node = ty.node;
        let data = match ty.data.clone() {
            TypeData::Ctor(TypeCtor { ty, params }) => {
                let ty = self.normalize0(ty, ctx);
                if params.is_empty() {
                    return ty;
                }
                TypeData::Ctor(TypeCtor {
                    ty,
                    params,
                })
            }
            TypeData::Incomplete(_) => unreachable!(),
            TypeData::Instance(TypeInstance { ty, args }) => {
                debug_assert!(matches!(self.type_(ty).data, TypeData::Ctor(_)) || args.is_empty());
                let ty = match &self.type_(ty).data {
                    TypeData::Ctor(TypeCtor { ty, params }) => {
                        let ty = self.type_(*ty);
                        self.bind_vars(params, &args, ctx);
                        ty.id
                    }
                    | TypeData::Fn(_)
                    | TypeData::Incomplete(_)
                    | TypeData::Instance(_)
                    | TypeData::Struct(_)
                    | TypeData::Var(_)
                    => ty,
                };
                let ty = self.normalize0(ty, ctx);
                return ty;
            }
            TypeData::Var(kind) => {
                let ty = match kind {
                    Var::Inference(_) => {
                        debug_assert!(!ctx.vars.contains_key(&ty.id));
                        assert_eq!(ty.id.0, self.package_id);
                        ctx.depends_on_inference_var = true;
                        return ty.id;
                    }
                    Var::Param => {
                        if let Some(&ty) = ctx.vars.get(&ty.id) {
                            ty
                        } else {
                            return ty.id;
                        }
                    }
                };
                return self.normalize0(ty, ctx);
            }
            TypeData::Fn(v) => {
                TypeData::Fn(self.normalize_fn(v, ctx))
            }
            TypeData::Struct(v) => {
                TypeData::Struct(self.normalize_struct(v, ctx))
            }
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
            assert!(ctx.vars.insert(param, arg).is_none());
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