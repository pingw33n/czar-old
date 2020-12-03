use super::{*, StructType};

#[derive(Default)]
struct Ctx {
    no_cache: bool,
    ext_vars: TypeSet,
}

impl PassImpl<'_> {
    pub fn normalize(&mut self, ty: TypeId) -> TypeId {
        if let Some(&norm_ty) = self.check_data.normalized_types.get(&ty) {
            debug_assert_eq!(self.normalize0(ty, &mut Ctx::default()), norm_ty);
            return norm_ty;
        }
        if let TypeData::Ctor(_) = &self.type_(ty).data {
            return ty;
        }
        let ctx = &mut Ctx::default();
        let norm_ty = self.normalize0(ty, ctx);
        debug_assert_eq!(self.normalize0(ty, &mut Ctx::default()), norm_ty);
        if !ctx.no_cache {
            self.insert_normalized_type(ty, norm_ty);
        }
        norm_ty
    }

    pub fn normalize_all(&mut self) {
        let types: Vec<_> = self.check_data.typings.values().copied().collect();
        for ty in types {
            self.normalize(ty);
        }
    }

    fn normalize0(&mut self, ty: TypeId, ctx: &mut Ctx) -> TypeId {
        self.normalize1(ty, TypeVarMap::default(), ctx)
    }

    fn normalize1(&mut self, mut ty: TypeId, mut vars: TypeVarMap, ctx: &mut Ctx) -> TypeId {
        let node = self.type_(ty).node;
        let ty = loop {
            let next_vars = match &self.type_(ty).data {
                TypeData::Ctor(_) => {
                    unreachable!()
                }
                TypeData::Incomplete(_) => unreachable!(),
                TypeData::Instance(TypeInstance { ty: next, args }) => {
                    match &self.type_(*next).data {
                        TypeData::Ctor(TypeCtor { ty: next, params }) => {
                            assert_eq!(args.len(), params.len());
                            let mut next_vars = TypeVarMap::default();
                            for (&param, &arg) in params.iter().zip(args.iter()) {
                                next_vars.insert(param, arg);
                            }

                            ty = *next;

                            Some(next_vars)
                        }
                        | TypeData::Fn(_)
                        | TypeData::Incomplete(_)
                        | TypeData::Instance(_)
                        | TypeData::GenericEnv(_)
                        | TypeData::Struct(_)
                        | TypeData::Var(_)
                        => {
                            assert!(args.is_empty());
                            ty = *next;
                            None
                        }
                    }
                }
                | TypeData::GenericEnv(_)
                | TypeData::Fn(_)
                | TypeData::Struct(_)
                => break ty,
                &TypeData::Var(var) => {
                    match var {
                        Var::Inference(_) => break ty,
                        Var::Param(_) => {
                            if let Some(next) = vars.get(ty) {
                                if next == ty {
                                    break ty;
                                }
                                vars.clear();
                                ty = next;
                                None
                            } else {
                                ctx.ext_vars.insert(ty);
                                break ty;
                            }
                        }
                    }
                }
            };
            if let Some(mut next_vars) = next_vars {
                for (_, val) in next_vars.iter_mut() {
                    *val = self.normalize1(*val, vars.clone(), ctx);
                }
                vars = next_vars;
            }
        };
        let norm_ty = match self.type_(ty).data.clone() {
            TypeData::GenericEnv(GenericEnv { ty, vars: mut genv_vars }) => {
                for (_, val) in genv_vars.iter_mut() {
                    let v = vars.get(*val).unwrap_or(*val);
                    *val = self.normalize1(v, vars.clone(), ctx);
                }
                let data = self.type_(ty).data.clone();
                let (ty, make_genv) = self.normalize_data(node, ty, data, &vars, ctx);
                assert!(make_genv);
                self.type_data_id(node, TypeData::GenericEnv(GenericEnv {
                    ty,
                    vars: genv_vars,
                }))
            }
            | data @ TypeData::Fn(_)
            | data @ TypeData::Struct(_)
            | data @ TypeData::Var(_)
            => {
                let (ty, make_genv) = self.normalize_data(node, ty, data, &vars, ctx);
                for (_, val) in vars.iter_mut() {
                    *val = self.normalize0(*val, ctx);
                }
                if make_genv {
                    let nominal_fn = self.type_(ty).data.as_fn().and_then(|v| v.name).is_some();
                    if nominal_fn {
                        for var in ctx.ext_vars.drain() {
                            vars.insert(var, var);
                        }
                    }
                    self.type_data_id(node, TypeData::GenericEnv(GenericEnv {
                        ty,
                        vars,
                    }))
                } else {
                    ty
                }
            }
            | TypeData::Ctor(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            => unreachable!(),
        };

        if !ctx.no_cache {
            self.insert_normalized_type(norm_ty, norm_ty);
        }

        norm_ty
    }

    fn normalize_data(&mut self,
        node: GlobalNodeId,
        ty: TypeId,
        data: TypeData,
        vars: &TypeVarMap,
        ctx: &mut Ctx,
    ) -> (TypeId, bool) {
        match data {
            TypeData::Fn(v) => {
                let data = TypeData::Fn(self.normalize_fn(v, vars, ctx));
                (self.type_data_id(node, data), true)
            }
            TypeData::Struct(v) => {
                let def = v.name.is_some();
                let data = TypeData::Struct(self.normalize_struct(v, vars, ctx));
                (self.type_data_id(node, data), def)
            }
            TypeData::Var(var) => {
                ctx.no_cache |= var.as_inference().is_some();
                (ty, false)
            }
            | TypeData::Ctor(_)
            | TypeData::GenericEnv(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            => unreachable!(),
        }
    }

    fn type_data_id(&mut self, node: GlobalNodeId, data: TypeData) -> TypeId {
        match self.type_data_ids.entry(data) {
            hash_map::Entry::Occupied(e) => {
                *e.get()
            }
            hash_map::Entry::Vacant(e) => {
                let ty = self.check_data.insert_type(node, e.key().clone());
                *e.insert(ty)
            }
        }
    }

    fn normalize_fn(&mut self, mut fn_: FnType, vars: &TypeVarMap, ctx: &mut Ctx) -> FnType {
        let FnType {
            name: _,
            params,
            result,
            unsafe_: _,
        } = &mut fn_;

        for param in params {
            *param = self.normalize1(*param, vars.clone(), ctx);
        }
        *result = self.normalize1(*result, vars.clone(), ctx);

        fn_
    }

    fn normalize_struct(&mut self, mut sty: StructType, vars: &TypeVarMap, ctx: &mut Ctx) -> StructType {
        let StructType {
            name: _,
            fields,
        } = &mut sty;

        for field in fields {
            field.ty = self.normalize1(field.ty, vars.clone(), ctx);
        }

        sty
    }

    fn insert_normalized_type(&mut self, ty: TypeId, norm_ty: TypeId) {
        let existing = self.check_data.normalized_types.insert(ty, norm_ty);
        assert!(existing.is_none() || existing == Some(norm_ty));
        if ty != norm_ty {
            let existing = self.check_data.normalized_types.insert(norm_ty, norm_ty);
            assert!(existing.is_none() || existing == Some(norm_ty));
        }
    }
}