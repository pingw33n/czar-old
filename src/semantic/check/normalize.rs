use super::{*, StructType};

impl PassImpl<'_> {
    pub fn normalize(&mut self, ty: TypeId) -> TypeId {
        self.normalize0(ty, Vec::new(), Vec::new())
    }

    pub fn normalize_all(&mut self) {
        let types: Vec<_> = self.check_data.types().map(|ty| ty.id).collect();
        for ty in types {
            self.normalize(ty);
        }
    }

    fn normalize0(&mut self, ty: TypeId, args: Vec<TypeId>, params: Vec<TypeId>) -> TypeId {
        let typ = self.type_(ty);
        let node = typ.node();
        let data = match typ.data.clone() {

            TypeData::Base(_) => {
                assert!(params.is_empty());
                debug_assert_eq!(args.len(), self.type_params(ty).len());
                if args.is_empty() {
                    return ty;
                } else {
                    TypeData::Instance(TypeInstance {
                        ty,
                        data: TypeInstanceData::Args(args),
                    })
                }
            }
            TypeData::Fn(v) => {
                assert!(params.is_empty());
                TypeData::Fn(self.normalize_fn(v, args))
            },
            TypeData::Incomplete(_) => unreachable!(),
            TypeData::Instance(TypeInstance {
                ty,
                data,
            }) => {
                return match data {
                    TypeInstanceData::Args(mut iargs) => {
                        for iarg in &mut iargs {
                            if let Some(i) = params.iter().position(|&p| p == *iarg) {
                                *iarg = args[i];
                            }
                        }
                        self.normalize0(ty, iargs, Vec::new())
                    }
                    TypeInstanceData::Params(iparams) => {
                        assert!(params.is_empty());
                        assert_eq!(args.len(), iparams.len());
                        self.normalize0(ty, args, iparams)
                    }
                }
            }
            TypeData::Struct(v) => {
                assert!(params.is_empty());
                TypeData::Struct(self.normalize_struct(v, args))
            }
            TypeData::Var => {
                assert!(params.is_empty());
                assert!(args.is_empty());
                return ty;
            }
        };

        match self.normalized_types.entry(data) {
            hash_map::Entry::Occupied(e) => {
                *e.get()
            }
            hash_map::Entry::Vacant(e) => {
                let ty = self.check_data.insert_type(node, e.key().clone());
                *e.insert(ty)
            }
        }
    }

    fn normalize_many(&mut self, tys: &mut [TypeId]) {
        for ty in tys {
            *ty = self.normalize(*ty);
        }
    }

    fn normalize_fn(&mut self, mut fn_: FnType, args: Vec<TypeId>) -> FnType {
        let FnType {
            params,
            ty_params,
            result,
            unsafe_: _,
        } = &mut fn_;

        assert_eq!(args.len(), ty_params.len());

        self.normalize_many(params);
        self.normalize_many(ty_params);
        *result = self.normalize(*result);

        fn_
    }

    fn normalize_struct(&mut self, mut sty: StructType, args: Vec<TypeId>) -> StructType {
        let StructType {
            fields,
        } = &mut sty;

        assert!(args.is_empty());

        for field in fields {
            field.ty = self.normalize(field.ty);
        }

        sty
    }
}