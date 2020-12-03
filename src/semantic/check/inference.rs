use super::*;

#[derive(Clone, Copy, Debug, EnumAsInner, Eq, Hash, PartialEq)]
pub enum InferenceVar {
    Any,
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
        let dst_var = self.underlying_type(dst).data.as_inference_var();
        match (src_var, dst_var) {
            | (Some(InferenceVar::Any), None)
            | (Some(InferenceVar::Any), Some(InferenceVar::Number(_)))
            => true,
            (Some(InferenceVar::Number(src_num)), None)
                if Some(src_num) == self.as_any_number(dst)
                => true,
            (Some(InferenceVar::Number(src_num)), Some(InferenceVar::Number(dst_num)))
                if src_num == dst_num
                => true,
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

    fn unify0(&mut self, ty1: TypeId, ty2: TypeId) {
        if ty1 == ty2 {
            return;
        }
        if self.unify_var(ty1, ty2) {
        } else if self.unify_var(ty2, ty1) {
        } else {
            match (&self.underlying_type(ty1).data, &self.underlying_type(ty2).data) {
                (TypeData::Struct(StructType { def: def1, fields: fields1 }),
                    TypeData::Struct(StructType { def: def2, fields: fields2 }))
                    if def1.is_some() && def1 == def2
                        || def1.is_none() && def2.is_none()
                        && fields1.len() == fields2.len()
                        && fields1.iter().zip(fields2.iter())
                            .all(|(s, d)| s.name == d.name)
                => {
                    let fields: Vec<_> = fields1.iter().zip(fields2.iter())
                        .map(|(s, d)| (s.ty, d.ty))
                        .collect();
                    for (ty1, ty2) in fields {
                        self.unify(ty1, ty2);
                    }
                }
                _ => {},
            }
        }
    }

    pub fn unify(&mut self, ty1: TypeId, ty2: TypeId) {
        let ty1 = self.normalize(ty1);
        let ty2 = self.normalize(ty2);
        self.unify0(ty1, ty2);
    }

    pub fn begin_inference(&mut self) {
        self.inference_ctxs.push(InferenceCtx::default());
    }

    pub fn finish_inference(&mut self) {
        for id in self.inference_ctx().vars.iter().copied().collect::<Vec<_>>() {
            match self.type_((self.package_id, id)).data.as_inference_var().unwrap() {
                InferenceVar::Any => {
                    let ty = self.type_((self.package_id, id));
                    assert!(ty.data.as_var().is_some());
                    assert_eq!(ty.node.0, self.package_id);
                    self.error(ty.node.1, "can't infer type".into());
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