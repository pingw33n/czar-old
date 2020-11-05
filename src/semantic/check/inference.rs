use super::*;

#[derive(Debug, EnumAsInner)]
pub enum InferenceVar {
    Any,
    Number(NumberKind),
}

#[derive(Default)]
pub struct InferenceCtx {
    vars: HashMap<LocalTypeId, InferenceVar>,
}

impl InferenceCtx {
    fn insert(&mut self, id: LocalTypeId, var: InferenceVar) {
        assert!(self.vars.insert(id, var).is_none());
    }

    fn get(&self, id: LocalTypeId) -> Option<&InferenceVar> {
        self.vars.get(&id)
    }

    fn remove(&mut self, id: LocalTypeId) {
        assert!(self.vars.remove(&id).is_some())
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
    pub fn new_inference_var(&mut self, node: NodeId, var: InferenceVar) -> TypeId {
        let ty = self.check_data.insert_type((self.package_id, node), TypeData::Var);
        self.inference_ctx_mut().insert(ty.1, var);
        ty
    }

    fn try_unify(&mut self, src: TypeId, dst: TypeId) -> bool {
        let src = self.unwrap_type(src).id();
        let src_var = self.inference_var(src);
        let dst_var = self.inference_var(dst);
        let can = match (src_var, dst_var) {
            (Some(InferenceVar::Any), None) => true,
            (Some(&InferenceVar::Number(src_num)), None)
                if Some(src_num) == self.as_any_number(dst)
                => true,
            (Some(&InferenceVar::Number(src_num)), Some(&InferenceVar::Number(dst_num)))
                if src_num == dst_num
                => true,
            _ => false,
        };
        if can {
            assert_eq!(src.0, self.package_id);
            self.check_data.finish_inference_var(src.1, dst, );
            self.inference_ctx_mut().remove(src.1);
            true
        } else {
            false
        }
    }

    pub fn unify(&mut self, ty1: TypeId, ty2: TypeId) -> (TypeId, TypeId) {
        // if ty1 == ty2 {
        //     return (ty1, ty2);
        // }
        // let ty1 = self.type_(ty1).id();
        // if ty1 == ty2 {
        //     return (ty2, ty2);
        // }
        // let ty2 = self.type_(ty2).id();
        // if ty1 == ty2 {
        //     return (ty1, ty1);
        // }
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
        for (id, var) in self.inference_ctxs.pop().unwrap().vars {
            match var {
                InferenceVar::Any => {
                    let ty = self.type_((self.package_id, id));
                    assert!(ty.data.as_var().is_some());
                    assert_eq!(ty.node().0, self.package_id);
                    self.error(ty.node().1, "can't infer type".into());
                }
                InferenceVar::Number(n) => {
                    let fallback = match n {
                        NumberKind::Int => PrimitiveType::I32,
                        NumberKind::Float => PrimitiveType::F64,
                    };
                    let fallback = self.std().type_(LangItem::Primitive(fallback));
                    self.check_data.finish_inference_var(id, fallback);
                }
            }
        }
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

    pub fn try_inference_var(&self, ty: TypeId) -> Option<&InferenceVar> {
        let ctx = self.try_inference_ctx()?;
        if ty.0 == self.package_id {
            ctx.get(ty.1)
        } else {
            None
        }
    }

    pub fn inference_var(&self, ty: TypeId) -> Option<&InferenceVar> {
        let ctx = self.inference_ctx();
        if ty.0 == self.package_id {
            ctx.get(ty.1)
        } else {
            None
        }
    }
}