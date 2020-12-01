use super::*;

#[derive(Debug)]
pub enum ImplValueItem {
    Single(NodeId),
    Fns(Vec<NodeId /*FnDef*/>),
}

#[derive(Debug)]
pub struct Impl {
    /// This is instance of type `Foo<T>` in `impl<T> Foo<T>`.
    for_ty: TypeId,
    values: HashMap<Ident, ImplValueItem>,
}

impl PassImpl<'_> {
    pub fn pre_check_impls(&mut self) -> Result<()> {
        for &impl_ in self.discover_data.impls() {
            let _ = self.ensure_typing(impl_);
        }
        Ok(())
    }

    pub fn check_impl(&mut self, node: NodeId /*Impl*/) -> Result<()> {
        let unit_ty = self.std().unit_type();
        self.check_data.insert_typing(node, unit_ty);

        let hir::Impl {
            ty_params,
            trait_,
            for_,
            items,
        } = self.hir.impl_(node);
        if trait_.is_some() {
            todo!();
        }

        let mut err = self.ensure_typing_many(ty_params).is_err();

        self.reso_ctxs.push(ResoCtx::Type);
        let for_ty = self.ensure_typing(*for_);
        assert_eq!(self.reso_ctxs.pop().unwrap(), ResoCtx::Type);
        let for_ty = for_ty?;
        let for_ty = self.type_(for_ty).data.as_ctor().unwrap().ty;

        let def = if let Some(def) = self.underlying_type(for_ty).data.def() {
            if def.0 != self.package_id {
                self.error(*for_,
                    "cannot define inherent `impl` for a type from outside of this package".into());
                err = true;
            }
            def
        } else {
            self.error(*for_,
                "can't define inherent `impl` on a type parameter".into());
            return Err(());
        };

        let mut dup_items = Vec::new();
        let impls = self.check_data.impls.entry(def)
            .or_insert_with(Vec::new);
        let mut impl_values = HashMap::with_capacity(items.len());
        for &item in items {
            match self.hir.node_kind(item).value {
                NodeKind::FnDef => {
                    let name = &self.hir.fn_def(item).name;
                    let sign = self.discover_data.fn_def_signature(item);
                    let mut dup = false;
                    for impl_ in &*impls {
                        match impl_.values.get(&name.value) {
                            Some(ImplValueItem::Single(_)) => {
                                dup = true;
                                break;
                            }
                            Some(ImplValueItem::Fns(fns)) => {
                                debug_assert!(!fns.iter().any(|&n| n == item));
                                let discover_data = self.discover_data;
                                if fns.iter().any(|&n| discover_data.fn_def_signature(n) == sign) {
                                    dup = true;
                                    break;
                                }
                            }
                            None => {}
                        }
                    }

                    if !dup {
                        match impl_values.entry(name.value.clone()) {
                            hash_map::Entry::Occupied(mut e) => {
                                match e.get_mut() {
                                    ImplValueItem::Single(_) => {
                                        dup = true;
                                    }
                                    ImplValueItem::Fns(fns) => {
                                        debug_assert!(!fns.iter().any(|&n| n == item));
                                        let discover_data = self.discover_data;
                                        if fns.iter().any(|&n| discover_data.fn_def_signature(n) == sign) {
                                            dup = true;
                                        } else {
                                            fns.push(item);
                                        }
                                    }
                                }
                            }
                            hash_map::Entry::Vacant(e) => {
                                e.insert(ImplValueItem::Fns(vec![item]));
                            }
                        };
                    }
                    if dup {
                        err = true;
                        dup_items.push(item);
                    }
                }
                _ => unreachable!(),
            }
        }
        impls.push(Impl {
            for_ty,
            values: impl_values,
        });
        for item in dup_items {
            let name = &self.hir.fn_def(item).name;
            let sign = self.discover_data.fn_def_signature(item);
            self.error_span(item, name.span, format!(
                "function `{}` is defined multiple times across inherent `impl`s",
                sign.display_with_name(&name.value)));
        }
        if err {
            Err(())
        } else {
            Ok(())
        }
    }

    pub fn check_impl_fn(&mut self,
        ty: TypeId,
        name: PathItem,
        sign: &FnParamsSignature,
    ) -> Result<Option<(GlobalNodeId, TypeId)>> {
        let in_pkg = |
            package_id: PackageId,
            discover_data: &DiscoverData,
            check_data: &CheckData,
        | -> Result<Option<(GlobalNodeId, TypeId)>> {
            let def = if let Some(v) = self.underlying_type(ty).data.def() {
                v
            } else {
                return Ok(None)
            };
            if let Some(impls) = check_data.impls.get(&def) {
                assert!(!impls.is_empty());
                for impl_ in impls {
                    if let Some(item) = impl_.values.get(&name.name.value) {
                        match item {
                            ImplValueItem::Single(_) => return Err(()),
                            ImplValueItem::Fns(fn_defs) => {
                                if let Some(&fn_def) = fn_defs.iter().find(|&&n| discover_data.fn_def_signature(n) == sign) {
                                    return Ok(Some(((package_id, fn_def), impl_.for_ty)));
                                }
                            }
                        }
                    }
                }
            }
            Ok(None)
        };
        let (fn_def, for_ty) = 'outer: loop {
            match in_pkg(self.package_id, self.discover_data, self.check_data) {
                Ok(Some(v)) => break 'outer v,
                Ok(None) => {}
                Err(()) => return Ok(None),
            }
            for package in self.packages.iter() {
                match in_pkg(package.id, &package.discover_data, &package.check_data) {
                    Ok(Some(v)) => break 'outer v,
                    Ok(None) => {}
                    Err(()) => return Ok(None),
                }
            }
            return Ok(None);
        };

        let fn_ty = self.ensure_typing_global(fn_def)?;
        let fn_ty = self.check_path_ty_args(&[name], fn_ty, true)?;
        let fn_ty = self.normalize(fn_ty);

        let for_ty = self.normalize(for_ty);
        let mut genv_vars = TypeVarMap::default();
        let ty = self.normalize(ty);
        let ty_genv_vars = &self.type_(ty).data.as_generic_env().unwrap().vars;
        let mut eq_vars = Vec::new();
        for (var, val) in self.type_(for_ty).data.as_generic_env().unwrap().vars.iter() {
            let from_var = self.type_param(val).unwrap().id;
            let var = ty_genv_vars.get(var).unwrap();
            if let Some(var2) = genv_vars.replace(from_var, var) {
                eq_vars.push((var, var2));
            }
        }
        for (var1, var2) in eq_vars {
            self.unify(var1, var2);
            debug_assert_eq!(self.normalize(var1), self.normalize(var2));
        }

        let fn_ty_node = self.type_(fn_ty).node;
        let fn_ty = self.check_data.insert_type(fn_ty_node, TypeData::Ctor(TypeCtor {
            ty: fn_ty,
            params: genv_vars.vars().collect(),
        }));
        let fn_ty = self.check_data.insert_type(fn_ty_node, TypeData::Instance(TypeInstance {
            ty: fn_ty,
            args: genv_vars.vals().collect(),
        }));

        Ok(Some((fn_def, fn_ty)))
    }
}