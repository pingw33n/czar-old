use super::*;

impl PassImpl<'_> {
    pub fn check_path(&mut self, node: NodeId /*PathEndEmpty|PathEndIdent|PathEndStar*/) -> Result<Option<TypeId>> {
        // Check `use {self}` case.
        if_chain! {
            if let Some(path_end_ident) = self.hir.try_path_end_ident(node);
            if self.discover_data.find_use_node(node, self.hir).is_some();
            let ident = &path_end_ident.item.ident;
            if ident.value.is_self_lower();
            if self.hir.path_segment(self.discover_data.parent_of(node)).prefix.is_empty();
            then {
                self.error_span(node, ident.span,
                    "`self` import can only be used in path with prefix".into());
                return Ok(None)
            }
        }

        let reso = self.resolver().resolve_node(node)?;
        assert!(!reso.is_empty());
        match reso.kind() {
            ResolutionKind::Exact => {
                if self.reso_ctx() == ResoCtx::Import {
                    Ok(None)
                } else {
                    self.check_path0(node, reso).map(Some)
                }
            }
            ResolutionKind::Empty => return Ok(None),
            ResolutionKind::Wildcard => {
                if !reso.nodes()
                    .all(|(_, (pkg, _))| pkg == self.package_id)
                {
                    self.error(node,
                        "only symbols from current package can be imported by wildcard import".into());
                }
                Ok(None)
            }
            ResolutionKind::Type => {
                let (k, type_) = reso.nodes().exactly_one().unwrap();
                assert_eq!(k, NsKind::Type);
                if self.reso_ctx() == ResoCtx::Import {
                    if reso.type_path().len() > 1 {
                        self.error(node,
                            "can't import associated items".into());
                    }
                    Ok(None)
                } else {
                    self.check_type_path(node, type_, reso.type_path()).map(Some)
                }
            }
        }
    }

    pub fn check_path_start(&mut self, node: NodeId /*Path*/) -> Result<Option<TypeId>> {
        let segment = self.hir.path(node).segment;
        Ok(if self.typing_state(segment) == Some(TypingState::Failed) {
            return Err(())
        } else if let Some(target) = self.check_data.try_target_of(segment) {
            if self.check_data(target.0).is_lvalue(target.1) {
                self.check_data.set_lvalue(node);
            }
            self.check_data.insert_path_to_target(node, target);
            Some(self.typing(segment)?)
        } else {
            None
        })
    }

    pub fn check_path_segment(&mut self, node: NodeId /*PathSegment*/) -> Result<Option<TypeId>> {
        let suffix = &self.hir.path_segment(node).suffix;
        Ok(if suffix.len() == 1 {
            if self.typing_state(suffix[0]) == Some(TypingState::Failed) {
                return Err(())
            } else if let Some(target) = self.check_data.try_target_of(suffix[0]) {
                self.check_data.insert_path_to_target(node, target);
                Some(self.typing(suffix[0])?)
            } else {
                None
            }
        } else {
            None
        })
    }

    fn check_path0(&mut self, path: NodeId /*PathEndIdent*/, reso: Resolution) -> Result<TypeId> {
        let reso_ctx = self.reso_ctx();
        let span = self.hir.path_end_ident(path).item.ident.span;
        let (pkg, node) = {
            // Check if we're resolving FnCall's callee.
            let fn_call = if_chain! {
                if reso_ctx == ResoCtx::Value;
                if let Some(fn_call) = self.discover_data.find_fn_call(path, self.hir);
                then {
                    Some((FnParamsSignature::from_call(fn_call, self.hir), self.hir.node_kind(fn_call).span))
                } else {
                    None
                }
            };
            if let Some((call_sign, call_span)) = fn_call {
                let mut found = None;
                // Function (base) name if there's at least one found.
                let mut name = None;
                // TODO Make this O(1)
                for node in reso.ns_nodes(NsKind::Value) {
                    if let Some(sign) = self.discover_data(node.0)
                        .try_fn_def_signature(node.1)
                    {
                        if name.is_none() {
                            name = Some(self.hir(node.0).fn_def(node.1).name.value.clone());
                        } else {
                            debug_assert_eq!(&self.hir(node.0).fn_def(node.1).name.value, name.as_ref().unwrap());
                        }
                        if &call_sign == sign {
                            found = Some(node);
                            break;
                        }
                    }
                }
                if let Some(found) = found {
                    found
                } else {
                    if let Some(name) = &name {
                        // There are other fns with the same name but none with matching signature.
                        self.error_span(path, call_span, format!(
                            "couldn't find function `{}`: none of existing functions matches the signature",
                            call_sign.display_with_name(name)));
                        return Err(());
                    }
                    if let Some(node) = reso.ns_nodes(NsKind::Value).next() {
                        // Could be a variable.
                        node
                    } else {
                        let node = reso.ns_nodes(NsKind::Type).next().unwrap();
                        self.error_span(path, span, format!(
                            "expected function but found {}",
                            self.describe_named(node)));
                        return Err(());
                    }
                }
            } else {
                let ns_kind = reso_ctx.to_ns_kind().unwrap();
                let mut it = reso.ns_nodes(ns_kind);
                if let Some(node) = it.next() {
                    if let Some(FnDef { name, .. }) = self.hir(node.0).try_fn_def(node.1) {
                        let text = if it.next().is_none() {
                            let sign = self.discover_data(node.0).fn_def_signature(node.1);
                            format!("invalid function reference, must include function's signature: `{}`",
                                sign.display_with_name(&name.value))
                        } else {
                            "invalid function reference, must include function's signature".into()
                        };
                        self.error_span(path, span, text);
                        return Err(());
                    } else {
                        assert!(it.next().is_none());
                    }
                    node
                } else {
                    let node = reso.nodes().next().unwrap().1;
                    let node = self.describe_named(node);
                    let exp_str = match ns_kind {
                        NsKind::Type => "type expression",
                        NsKind::Value => "expression",
                    };
                    self.error_span(path, span, format!(
                        "expected {}, found {}", exp_str, node));
                    return Err(());
                }
            }
        };
        self.check_data.insert_path_to_target(path, (pkg, node));
        let ty = if pkg == self.package_id {
            if let Some(ty) = self.ensure_opt_typing(node)? {
                ty
            } else {
                self.error_span(path, span, format!(
                    "expected type, found {}", self.describe_named((pkg, node))));
                return Err(());
            }
        } else {
            self.packages[pkg].check_data.typing(node)
        };
        let ty = self.check_path_node_ty_args(path, ty)?;
        Ok(ty)
    }

    fn check_path_node_ty_args(&mut self, path: NodeId /*PathEndIdent*/, ty: TypeId) -> Result<TypeId> {
        let path_start = self.discover_data.find_path_start(path, self.hir).unwrap();

        let fully_inferrable = match self.hir.node_kind(self.discover_data.parent_of(path_start)).value {
            | NodeKind::FnCall
            | NodeKind::StructLiteral
            => true,
            _ => false,
        };

        let path = PathItem::from_hir_path_end(path, self.hir, self.discover_data);
        let ty = self.check_path_ty_args(&path, ty, fully_inferrable)?;
        Ok(ty)
    }

    pub fn check_path_ty_args(&mut self, path: &[PathItem], ty: TypeId, fully_inferrable: bool) -> Result<TypeId> {
        assert!(!path.is_empty());
        let args = Self::path_ty_args(path);

        let mut err = false;
        let param_count = self.type_(ty).data.type_params().len();
        if args.is_some() || !fully_inferrable {
            let (arg_count, span) = args.map(|v| (v.value.len(), v.span))
                .unwrap_or_else(|| (0, self.hir.node_kind(path.last().unwrap().node).span));
            if arg_count != param_count {
                if param_count == 0 {
                    self.error_span(path[0].node, span, format!(
                        "unexpected type arguments: type `{}` doesn't have type parameters",
                        self.display_type(ty)));
                } else {
                    self.error_span(path[0].node, span, format!(
                        "wrong number of type arguments: expected {}, found {}",
                        param_count, arg_count));
                }
                err = true;
            }
        }
        if err {
            return Err(());
        }
        let ty_args = self.build_path_ty_args(path, ty)?;

        let ty = self.insert_type((self.package_id, path.last().unwrap().node),
            TypeData::Instance(TypeInstance {
                ty,
                args: ty_args,
            }));

        Ok(ty)
    }

    fn build_path_ty_args(&mut self, path: &[PathItem], ty: TypeId) -> Result<Vec<TypeId>> {
        let params = self.type_(ty).data.type_params();
        if params.is_empty() {
            return Ok(Vec::new());
        }
        let mut err = false;
        let mut r = Vec::with_capacity(params.len());
        let args = Self::path_ty_args(path);
        if let Some(args) = args {
            assert_eq!(args.value.len(), params.len());
            for &arg in args.value {
                // TODO check for any type `_`
                if let Ok(ty) = self.typing(arg) {
                    r.push(ty);
                } else {
                    err = true;
                }
            }
        } else {
            let node = path.last().unwrap().node;
            for _ in 0..params.len() {
                r.push(self.new_inference_var(node, InferenceVar::Any { inhabited: true }));
            }
        }
        if err {
            Err(())
        } else {
            Ok(r)
        }
    }
}