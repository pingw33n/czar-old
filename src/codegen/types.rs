use super::*;

#[derive(Clone, Copy)]
pub struct TypeLl {
    ty: TypeRef,
    /// `false` means the lower-level type was constructed from uninhabited type.
    inhabited: bool,
}

impl TypeLl {
    fn inhabited(&self) -> Result<TypeRef> {
        if self.inhabited {
            Ok(self.ty)
        } else {
            Err(())
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct GenericEnvId(TypeRef);

pub struct GenericEnv {
    pub id: GenericEnvId,
    pub vars: TypeVarMap,
}

impl Codegen<'_> {
    pub fn typing(&mut self, node: GlobalNodeId, genv: &GenericEnv) -> Result<TypeRef> {
        let ty = self.packages[node.0].check_data.typing(node.1);
        self.type_(ty, genv)
    }

    pub fn type_(&mut self, ty: TypeId, genv: &GenericEnv) -> Result<TypeRef> {
        self.type0(ty, genv).inhabited()
    }

    pub fn type_allow_uninhabited(&mut self, ty: TypeId, genv: &GenericEnv) -> TypeRef {
        self.type0(ty, genv).ty
    }

    pub fn lang_type(&mut self, lang_item: LangItem) -> TypeRef {
        assert_ne!(lang_item, LangItem::Primitive(PrimitiveType::Never));
        self.type_(self.packages.std().check_data.lang().type_(lang_item), &self.default_genv()).unwrap()
    }

    pub fn make_genv_id(&mut self, ty_vars: &TypeVarMap, genv: &GenericEnv) -> Result<GenericEnvId> {
        let mut ty_vars: Vec<_> = ty_vars.iter().collect();
        ty_vars.sort_by_key(|&(k, _)| k);
        let mut genv_id = Vec::with_capacity(ty_vars.len());
        for (_, ty) in ty_vars {
            genv_id.push(self.type_(ty, genv)?);
        }
        Ok(GenericEnvId(self.make_struct_type0(None, &mut genv_id)))
    }

    pub fn default_genv(&self) -> GenericEnv {
        GenericEnv {
            id: GenericEnvId(self.llvm.struct_type(&mut [])),
            vars: TypeVarMap::default(),
        }
    }

    pub fn normalized(&self, ty: TypeId) -> TypeId {
        self.packages[ty.0].check_data.normalized_type(ty)
    }

    pub fn find_type_param_deps(&self, ty: TypeId) -> Vec<TypeId> {
        let mut r = Vec::new();
        self.find_type_param_deps0(ty, &mut r);
        r
    }

    fn find_type_param_deps0(&self, ty: TypeId, r: &mut Vec<TypeId>) {
        match &self.packages.type_(ty).data {
            TypeData::GenericEnv(_) => {}
            TypeData::Fn(FnType { name, params, result, unsafe_: _ }) => {
                assert!(name.is_none());
                for &param in params {
                    self.find_type_param_deps0(param, r);
                }
                self.find_type_param_deps0(*result, r);
            }
            &TypeData::Slice(check::SliceType { item, len: _ }) => {
                self.find_type_param_deps0(item, r);
            }
            TypeData::Struct(check::StructType { name, fields }) => {
                assert!(name.is_none());
                for &check::StructTypeField { name: _, ty } in fields {
                    self.find_type_param_deps0(ty, r);
                }
            }
            TypeData::Var(Var::Param(_)) => r.push(ty),

            | TypeData::Ctor(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            | TypeData::Var(Var::Inference(_))
            => unreachable!(),
        }
    }

    pub fn resolve_fn_genv_vars(&self, ty: TypeId, outer: &GenericEnv) -> TypeVarMap {
        let mut r = self.packages.type_(ty).data.as_generic_env().map(|v| v.vars.clone()).unwrap_or_default();
        let mut more = Vec::new();
        for (_, val) in r.iter_mut() {
            if let Some(v) = outer.vars.get(*val) {
                *val = v;
            }
            more.extend_from_slice(&self.find_type_param_deps(*val));
        }
        for var in more {
            if r.get(var).is_none() {
                if let Some(val) = outer.vars.get(var) {
                    r.insert(var, val);
                }
            }
        }

        r
    }

    fn type0(&mut self, ty: TypeId, genv: &GenericEnv) -> TypeLl {
        let ty = self.normalized(ty);
        if let Some(&v) = self.types.get(&(ty, genv.id)) {
            return v;
        }
        let ty_ll = self.type1(ty, genv);
        assert!(self.types.insert((ty, genv.id), ty_ll).is_none());
        ty_ll
    }

    fn type1(&mut self, ty: TypeId, genv: &GenericEnv) -> TypeLl {
        let uty = self.packages.underlying_type(ty);
        match &uty.data {
            TypeData::Fn(FnType { name: _, params, result, unsafe_: _, }) => {
                let mut inhabited = true;
                let param_tys = &mut Vec::with_capacity(params.len());
                for &param in params {
                    let ty = self.type0(param, genv);
                    param_tys.push(ty.ty);
                    inhabited &= ty.inhabited;
                }
                let res_ty = self.type0(*result, genv).ty;
                TypeLl {
                    ty: TypeRef::function(res_ty, param_tys),
                    inhabited,
                }
            }
            TypeData::GenericEnv(check::GenericEnv { ty, vars: _ }) => self.type0(*ty, genv),
            TypeData::Slice(v) => self.make_slice_type(v, genv),
            TypeData::Struct(v) => self.make_struct_type(ty, v, genv),
            TypeData::Var(_) => {
                let ty = genv.vars.get(uty.id).unwrap();
                self.type0(ty, genv)
            },
            | TypeData::Ctor(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            => unreachable!("{:?}", uty),
        }
    }

    fn make_struct_type(&mut self, ty: TypeId, sty: &check::StructType, genv: &GenericEnv) -> TypeLl {
        let check::StructType { name: def, fields } = sty;
        if let Some(def) = *def {
            if let Some(prim) = self.packages.std().check_data.lang().as_primitive(def) {
                return self.make_prim_type(ty, prim, genv);
            }
        }
        let mut inhabited = true;
        let field_tys = &mut Vec::with_capacity(fields.len());
        for &check::StructTypeField { name: _, ty } in fields {
            let ty = self.type0(ty, genv);
            inhabited &= ty.inhabited;
            field_tys.push(ty.ty);
        }
        let ty = self.make_struct_type0(*def, field_tys);
        TypeLl {
            ty,
            inhabited,
        }
    }

    fn make_slice_type(&mut self, slt: &check::SliceType, genv: &GenericEnv) -> TypeLl {
        let &check::SliceType { item, len } = slt;
        let item = self.type_allow_uninhabited(item, genv);
        let ty = if let Some(len) = len {
            self.llvm.array_type(item, len)
        } else {
            self.llvm.struct_type(&mut [
                self.llvm.pointer_type(item),
                self.llvm.size_type(),
            ])
        };
        TypeLl {
            ty,
            inhabited: true,
        }
    }

    fn make_struct_type0(&mut self, def: Option<GlobalNodeId>, fields: &mut [TypeRef]) -> TypeRef {
        let shape = self.llvm.struct_type(fields);
        if let Some(def) = def {
            match self.defined_types.entry((def, GenericEnvId(shape))) {
                hash_map::Entry::Occupied(e) => {
                    *e.get()
                }
                hash_map::Entry::Vacant(e) => {
                    let name = &self.packages[def.0].hir.struct_(def.1).name.value;
                    let ty = self.llvm.named_struct_type(name, fields);
                    e.insert(ty);
                    ty
                }
            }
        } else {
            shape
        }
    }

    fn make_prim_type(&mut self, ty: TypeId, prim_ty: PrimitiveType, genv: &GenericEnv) -> TypeLl {
        use PrimitiveType::*;
        let ty = match prim_ty {
            Bool => self.llvm.int_type(1),
            F32 => self.llvm.float_type(),
            F64 => self.llvm.double_type(),
            I8 | U8 => self.llvm.int_type(8),
            I16 | U16 => self.llvm.int_type(16),
            I32 | U32 | Char => self.llvm.int_type(32),
            I64 | U64 => self.llvm.int_type(64),
            I128 | U128 => self.llvm.int_type(128),
            ISize | USize => self.llvm.size_type(),
            Never => return TypeLl {
                ty: self.llvm.struct_type(&mut []),
                inhabited: false,
            },
            Ptr => {
                let pty = self.packages.type_(ty).data.as_generic_env().unwrap().vars.vals().next().unwrap();
                let pty = self.type_allow_uninhabited(pty, genv);
                pty.pointer()
            }
        };
        TypeLl {
            ty,
            inhabited: true,
        }
    }
}