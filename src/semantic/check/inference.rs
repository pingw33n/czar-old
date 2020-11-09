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
            data: TypeInstanceData::Params(Vec::new()),
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

    fn try_unify(&mut self, src: TypeId, dst: TypeId) -> bool {
        let src = self.type_term(src).id;
        let src_var = self.type_(src).data.as_inference_var();
        let dst_var = self.type_(dst).data.as_inference_var();
        let can = match (src_var, dst_var) {
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
        };
        if can {
            assert_eq!(src.0, self.package_id);
            self.finish_inference_var(src.1, dst);
            true
        } else {
            false
        }
    }

    pub fn unify(&mut self, ty1: TypeId, ty2: TypeId) -> (TypeId, TypeId) {
        if self.try_unify(ty1, ty2) {
            (ty2, ty2)
        } else if self.try_unify(ty2, ty1) {
            (ty1, ty1)
        } else {
            (ty1, ty2)
        }
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