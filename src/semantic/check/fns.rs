use super::*;

impl PassImpl<'_> {
    pub fn pre_check_fn_def(&mut self, node: NodeId /*FnDef*/) -> Result<()> {
        let FnDef {
            name,
            vis: _,
            ty_params,
            params,
            ret_ty,
            unsafe_,
            variadic: _,
            body,
        } = self.hir.fn_def(node);
        if body.is_none() && unsafe_.is_none() {
            self.error_span(node, name.span,
                "external function must be marked as `unsafe`".into());
        }
        let params = self.ensure_typing_many(params);
        let result = if let Some(n) = *ret_ty {
            self.ensure_typing(n)
        } else {
            Ok(self.std().unit_type())
        };

        let ty_params = self.ensure_typing_many(ty_params);

        let ty = self.check_data.insert_type((self.package_id, node),
            TypeData::Fn(FnType {
                def: Some((self.package_id, node)),
                params: params?,
                result: result?,
                unsafe_: unsafe_.is_some(),
            }));

        let ty_params = ty_params?;
        self.insert_typing(node, TypeData::Ctor(TypeCtor {
            ty,
            params: ty_params,
        }));
        Ok(())
    }

    pub fn check_fn_def(&mut self, node: NodeId /*FnDef*/) -> Result<()> {
        let FnDef {
            name,
            ret_ty,
            body,
            .. } = self.hir.fn_def(node);
        let expected_ret_ty = if let Some(n) = *ret_ty {
            self.typing(n)?
        } else {
            self.std().unit_type()
        };
        if let Some(body) = *body {
            let actual_ret_ty = self.typing(body)?;
            self.unify(actual_ret_ty, expected_ret_ty);
            if self.normalize(actual_ret_ty) != self.normalize(expected_ret_ty) {
                let expr_node = self.hir.block(body).exprs.last()
                    .copied().unwrap_or(body);
                self.error(expr_node, format!(
                    "mismatching return types: function `{fname}::{fsign}` expects `{exp}`, found `{act}`",
                    fname=name.value, fsign= FnParamsSignature::from_def(node, self.hir),
                    exp=self.display_type(expected_ret_ty),
                    act=self.display_type(actual_ret_ty)));
            }
        }
        Ok(())
    }

    pub fn check_fn_def_param(&mut self, node: NodeId /*FnDefParam*/) -> Result<TypeId> {
        self.check_data.set_lvalue(node);
        self.typing(self.hir.fn_def_param(node).ty)
    }

    pub fn check_fn_call(&mut self, ctx: &HirVisitorCtx) -> Result<TypeId> {
        let FnCall {
            callee,
            kind,
            args,
        } = self.hir.fn_call(ctx.node);
        let (fn_def_node, fn_ty) = match *kind {
            FnCallKind::Free => {
                let callee_ty = self.typing(*callee)?;
                let callee_ty = self.normalize(callee_ty);
                let fn_def = if let Some(FnType { def, .. }) = self.underlying_type(callee_ty).data.as_fn() {
                    if def.is_none() {
                        todo!()
                    }
                    def.unwrap()
                } else {
                    self.error(*callee, format!(
                        "invalid callee type: expected function, found `{}`",
                        self.display_type(callee_ty)));
                    return Err(());
                };
                (fn_def, callee_ty)
            }
            FnCallKind::Method => self.check_method_call(ctx.node)?,
        };

        let fn_ty = self.normalize(fn_ty);
        let params = self.underlying_type(fn_ty).data.as_fn().unwrap().params.clone();
        assert_eq!(args.len(), params.len());

        for (arg, &param_ty) in args
            .iter()
            .zip(params.iter())
        {
            let arg_ty = if let Ok(ty) = self.typing(arg.value) {
                ty
            } else {
                continue;
            };
            self.unify(arg_ty, param_ty);
            if self.normalize(arg_ty) != self.normalize(param_ty) {
                let hir = self.hir(fn_def_node.0);
                let name = &hir.fn_def(fn_def_node.1).name.value;
                self.error(arg.value, format!(
                    "mismatching types in fn call of `{f}`: expected `{param}`, found `{arg}`",
                    f=FnParamsSignature::from_def(fn_def_node.1, hir).display_with_name(name),
                    param=self.display_type(param_ty), arg=self.display_type(arg_ty)));
            }
        }

        let res_ty = self.underlying_type(fn_ty).data.as_fn().unwrap().result;

        Ok(res_ty)
    }

    fn check_method_call(&mut self, fn_call: NodeId) -> Result<(GlobalNodeId, TypeId)> {
        let fnc = self.hir.fn_call(fn_call);
        assert_eq!(fnc.kind, FnCallKind::Method);

        let (path_end_node, path_end_item) = fnc.callee_path_item(self.hir);
        let name = &path_end_item.ident;

        let receiver = fnc.args[0].value;
        let receiver_ty = self.ensure_typing(receiver)?;

        if self.underlying_type(receiver_ty).data.as_inference_var().is_some() {
            self.error(receiver, "can't infer type".into());
            return Err(());
        }

        let fn_name = PathItem::from_hir(path_end_node, path_end_item);
        let sign = FnParamsSignature::from_call(fn_call, self.hir);
        if let Some((fn_def, fn_ty)) = self.check_impl_fn(receiver_ty, fn_name, &sign)? {
            self.check_data.insert_path_to_target(fnc.callee, fn_def);
            self.check_data.insert_typing(fnc.callee, fn_ty);

            Ok((fn_def, fn_ty))
        } else {
            self.error(fnc.callee, format!(
                "method `{}` not found for type `{}`",
                sign.display_with_name(&name.value),
                self.display_type(receiver_ty)));
            Err(())
        }
    }

    /// Performs type-based path resolution and checking.
    pub fn check_type_path(&mut self,
        full_path: NodeId /*PathEndIdent*/,
        type_: GlobalNodeId,
        path: &[PathItem],
    ) -> Result<TypeId> {
        assert!(path.len() > 1);

        let ty = self.ensure_typing_global(type_)?;

        debug_assert!(self.type_(ty).data.as_inference_var().is_none());

        let mut err = false;
        let ty = self.check_path_ty_args(&path[..1], ty, true)
            .unwrap_or_else(|_| {
                err = true;
                ty
            });
        let ty = self.normalize(ty);

        let item_name = &path[1].name;

        let r = if_chain! {
            if path.len() == 2;
            if let Some(fn_call) = self.discover_data.find_fn_call(full_path, self.hir);
            then {
                let sign = FnParamsSignature::from_call(fn_call, self.hir);
                if let Some((fn_def, fn_ty)) = self.check_impl_fn(ty, path[1].clone(), &sign)? {
                    self.check_data.insert_path_to_target(full_path, fn_def);
                    Ok(fn_ty)
                } else {
                    self.error_span(full_path, item_name.span, format!(
                        "associated function `{}` not found for type `{}`",
                        sign.display_with_name(&item_name.value),
                        self.display_type(ty)));
                    Err(())
                }
            } else {
                self.error_span(full_path, item_name.span, format!(
                    "associated item `{}` not found for type `{}`",
                    item_name.value, self.display_type(ty)));
                Err(())
            }
        };
        if err {
            Err(())
        } else {
            r
        }
    }
}