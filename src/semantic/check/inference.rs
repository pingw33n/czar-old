use super::*;

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, Hash, PartialEq)]
pub enum InferenceVar {
    Any {
        inhabited: bool,
    },
    Number(NumberKind),
}

#[derive(Default)]
pub struct InferenceCtx {
    vars: HashSet<LocalTypeId>,
}

impl InferenceCtx {
    fn insert(&mut self, id: LocalTypeId) {
        assert!(self.vars.insert(id));
    }

    fn remove(&mut self, id: LocalTypeId) {
        assert!(self.vars.remove(&id))
    }
}

impl CheckData {
    fn finish_inference_var(&mut self, var: LocalTypeId, ty: TypeId) {
        let vard = &mut self.type_mut(var).data;
        let old = std::mem::replace(vard, TypeData::Instance(TypeInstance {
            ty,
            args: Vec::new(),
        }));
        assert!(old.as_var().is_some());
    }
}

impl PassImpl<'_> {
    pub fn new_inference_var(&mut self, node: NodeId, kind: InferenceVar) -> TypeId {
        let ty = self.insert_type((self.package_id, node), TypeData::Var(Var::Inference(kind)));
        self.inference_ctx_mut().insert(ty.1);
        ty
    }

    pub fn can_unify_inference_var(&self, src: TypeId, dst: TypeId) -> bool {
        let src_var = self.underlying_type(src).data.as_inference_var();
        match src_var {
            Some(InferenceVar::Any { inhabited: true })
                => true,
            Some(InferenceVar::Any { inhabited: false })
                => !matches!(self.underlying_type(dst).data,
                    TypeData::Var(Var::Inference(InferenceVar::Any { inhabited: true }))),
            Some(InferenceVar::Number(src_num))
                => Some(src_num) == self.as_any_number(dst),
            _ => false,
        }
    }

    fn unify_var(&mut self, src: TypeId, dst: TypeId) -> bool {
        if self.can_unify_inference_var(src, dst) {
            assert_eq!(src.0, self.package_id);
            self.finish_inference_var(src.1, dst);
            true
        } else {
            false
        }
    }

    fn unify0(&mut self, ty1: TypeId, ty2: TypeId) -> bool {
        if ty1 == ty2 {
            return true
        }
        match (&self.type_(ty1).data, &self.type_(ty2).data) {
            (TypeData::GenericEnv(GenericEnv { ty: ty1, vars: vars1}),
                TypeData::GenericEnv(GenericEnv { ty: ty2, vars: vars2}))
            => {
                let ty1 = *ty1;
                let vars1 = vars1.clone();
                let ty2 = *ty2;
                let vars2 = vars2.clone();
                if self.unify0(ty1, ty2) {
                    assert_eq!(vars1.len(), vars2.len());
                    for ((var1, val1), (var2, val2)) in vars1.iter().zip(vars2.iter()) {
                        assert_eq!(var1, var2);
                        self.unify0(val1, val2);
                    }
                    true
                } else {
                    false
                }
            }
            (&TypeData::Slice(SliceType { item: item1, len: len1 }),
                &TypeData::Slice(SliceType { item: item2, len: len2 }))
            => {
                if len1 == len2 {
                    self.unify0(item1, item2)
                } else {
                    false
                }
            }
            (TypeData::Struct(StructType { name: name1, fields: fields1 }),
                TypeData::Struct(StructType { name: name2, fields: fields2 }))
            => {
                if name1.is_some() && name1 == name2
                    || name1.is_none() && name2.is_none()
                    && fields1.len() == fields2.len()
                    && fields1.iter().zip(fields2.iter())
                        .all(|(s, d)| s.name == d.name)
                {
                    let fields: Vec<_> = fields1.iter().zip(fields2.iter())
                        .map(|(s, d)| (s.ty, d.ty))
                        .collect();
                    for (ty1, ty2) in fields {
                        self.unify0(ty1, ty2);
                    }
                    true
                } else {
                    false
                }
            }
            // Instance on either side means unification has been already done (e.g. via struct field).
            (TypeData::Instance(_), _) | (_, TypeData::Instance(_)) => false,
            _ => self.unify_var(ty1, ty2) || self.unify_var(ty2, ty1),
        }
    }

    pub fn unify(&mut self, ty1: TypeId, ty2: TypeId) -> bool {
        let ty1 = self.normalize(ty1);
        let ty2 = self.normalize(ty2);
        self.unify0(ty1, ty2)
    }

    pub fn begin_inference(&mut self) {
        self.inference_ctxs.push(InferenceCtx::default());
    }

    pub fn finish_inference(&mut self) {
        for id in self.inference_ctx().vars.iter().copied().collect::<Vec<_>>() {
            match self.type_((self.package_id, id)).data.as_inference_var().unwrap() {
                InferenceVar::Any { inhabited: true } => {
                    let ty = self.type_((self.package_id, id));
                    assert!(ty.data.as_var().is_some());
                    assert_eq!(ty.node.0, self.package_id);
                    self.error(ty.node.1, "can't infer type".into());
                }
                InferenceVar::Any { inhabited: false } => {
                    let ty = self.std().type_(LangItem::Primitive(PrimitiveType::Never));
                    self.finish_inference_var(id, ty);
                }
                InferenceVar::Number(n) => {
                    let fallback = match n {
                        NumberKind::Int => PrimitiveType::I32,
                        NumberKind::Float => PrimitiveType::F64,
                    };
                    let fallback = self.std().type_(LangItem::Primitive(fallback));
                    self.finish_inference_var(id, fallback);
                }
            }
        }
    }

    fn finish_inference_var(&mut self, var: LocalTypeId, ty: TypeId) {
        self.check_data.finish_inference_var(var, ty);
        self.inference_ctx_mut().remove(var);
    }

    fn try_inference_ctx(&self) -> Option<&InferenceCtx> {
        self.inference_ctxs.last()
    }

    fn inference_ctx(&self) -> &InferenceCtx {
        self.try_inference_ctx().unwrap()
    }

    fn inference_ctx_mut(&mut self) -> &mut InferenceCtx {
        self.inference_ctxs.last_mut().unwrap()
    }
}