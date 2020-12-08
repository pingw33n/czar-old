use super::*;

#[derive(Debug)]
pub enum ImplValueItem {
    Single(NodeId),
    Fns(Vec<NodeId /*FnDef*/>),
}

#[derive(Debug)]
pub struct Impl {
    node: NodeId /*Impl*/,
    for_ty: TypeId,
    values: HashMap<Ident, ImplValueItem>,
}

#[derive(Default)]
pub struct Impls {
    nominal: HashMap<GlobalNodeId, Vec<Impl>>,
    structural: Vec<Impl>,
}

struct MatchTypeCtx<'a> {
    pat_package_id: PackageId,
    pat_params: &'a [NodeId],
    pat_vars: Vec<(TypeId, TypeId)>,
}

impl PassImpl<'_> {
    pub fn normalize_impls(&mut self) {
        let mut tys = Vec::new();
        for package in self.packages.iter() {
            for impls in package.check_data.impls.nominal.values() {
                for impl_ in impls {
                    tys.push(impl_.for_ty);
                }
            }
            for impl_ in &package.check_data.impls.structural {
                tys.push(impl_.for_ty);
            }
        }
        for ty in tys {
            self.normalize(ty);
        }
    }

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
        let for_ty = self.normalize(for_ty);

        let for_name = if let Some(name) = self.underlying_type(for_ty).data.name() {
            if name.0 != self.package_id {
                self.error(*for_,
                    "cannot define inherent `impl` for a type from outside of this package".into());
                err = true;
            }
            Some(name)
        } else if matches!(self.type_(for_ty).data, TypeData::Var(_)) {
            self.error(*for_,
                "can't define inherent `impl` on a type parameter".into());
            return Err(());
        } else {
            if !self.package_id.is_std() {
                self.error(*for_,
                    "cannot define inherent `impl` for a structural type".into());
                return Err(());
            }
            None
        };

        let impls = if let Some(name) = for_name {
            self.check_data.impls.nominal.entry(name)
                .or_insert_with(Vec::new);
            &self.check_data.impls.nominal[&name]
        } else {
            &self.check_data.impls.structural
        };

        let mut dup_items = Vec::new();
        let mut impl_values = HashMap::with_capacity(items.len());
        for &item in items {
            match self.hir.node_kind(item).value {
                NodeKind::FnDef => {
                    let name = &self.hir.fn_def(item).name;
                    let sign = self.discover_data.fn_def_signature(item);
                    let mut dup = false;
                    for impl_ in &*impls {
                        if self.match_type(for_ty, impl_.for_ty, (self.package_id, impl_.node)).is_none() {
                            continue;
                        }
                        match impl_.values.get(&name.value) {
                            Some(ImplValueItem::Single(_)) => {
                                dup = true;
                                break;
                            }
                            Some(ImplValueItem::Fns(fns)) => {
                                debug_assert!(!fns.iter().any(|&n| n == item));
                                if fns.iter().any(|&n| self.discover_data.fn_def_signature(n) == sign) {
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

        let impls = if let Some(name) = for_name {
            self.check_data.impls.nominal.get_mut(&name).unwrap()
        } else {
            &mut self.check_data.impls.structural
        };
        impls.push(Impl {
            node,
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
        let ty = self.normalize(ty);
        let ty_name = self.underlying_type(ty).data.name();

        struct Res {
            fn_def: GlobalNodeId,
            self_ty_vars: Vec<(TypeId, TypeId)>,
        }

        #[derive(Clone, Copy)]
        enum Error {
            FoundMany,
            NotFound,
            FoundOther,
        }

        let in_pkg = |
            package_id: PackageId,
            discover_data: &DiscoverData,
            check_data: &CheckData,
        | -> std::result::Result<Res, Error> {
            let impls = if let Some(name) = ty_name {
                if let Some(v) = check_data.impls.nominal.get(&name) {
                    v
                } else {
                    return Err(Error::NotFound);
                }
            } else {
                &check_data.impls.structural
            };
            let mut r = None;
            for impl_ in impls {
                let self_ty_vars = if let Some(v) = self.match_type(ty, impl_.for_ty, (package_id, impl_.node)) {
                    v
                } else {
                    continue;
                };
                if let Some(item) = impl_.values.get(&name.name.value) {
                    match item {
                        ImplValueItem::Single(_) => return Err(Error::FoundOther),
                        ImplValueItem::Fns(fn_defs) => {
                            if let Some(&fn_def) = fn_defs.iter().find(|&&n| discover_data.fn_def_signature(n) == sign) {
                                if r.is_some() {
                                    return Err(Error::FoundMany);
                                } else {
                                    r = Some(Res {
                                        fn_def: (package_id, fn_def),
                                        self_ty_vars,
                                    });
                                }
                            }
                        }
                    }
                }
            }
            r.ok_or(Error::NotFound)
        };
        const FOUND_MANY_ERR_TEXT: &str = "multiple applicable items are in scope";
        let Res { fn_def, self_ty_vars } = 'outer: loop {
            match in_pkg(self.package_id, self.discover_data, self.check_data) {
                Ok(v) => break 'outer v,
                Err(Error::NotFound) => {}
                Err(Error::FoundMany) => {
                    self.error_span(name.node, name.name.span, FOUND_MANY_ERR_TEXT.into());
                    return Err(());
                }
                Err(Error::FoundOther) => return Ok(None),
            }
            for package in self.packages.iter() {
                match in_pkg(package.id, &package.discover_data, &package.check_data) {
                    Ok(v) => break 'outer v,
                    Err(Error::NotFound) => {}
                    Err(Error::FoundMany) => {
                        self.error_span(name.node, name.name.span, FOUND_MANY_ERR_TEXT.into());
                        return Err(());
                    }
                    Err(Error::FoundOther) => return Ok(None),
                }
            }
            return Ok(None);
        };

        let fn_ty = self.ensure_typing_global(fn_def)?;
        let fn_ty = self.check_path_ty_args(&[name], fn_ty, true)?;
        let fn_ty = self.normalize(fn_ty);

        let mut genv_vars = TypeVarMap::default();
        for (var, val) in self_ty_vars {
            if let Some(val2) = genv_vars.replace(var, val) {
                self.unify(val, val2);
                debug_assert_eq!(self.normalize(val), self.normalize(val2));
            }
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

    fn match_type(&self, ty: TypeId, pat: TypeId, impl_: GlobalNodeId /*Impl*/) -> Option<Vec<(TypeId, TypeId)>> {
        let pat = self.check_data.normalized_type(pat);
        let mut ctx = MatchTypeCtx {
            pat_package_id: impl_.0,
            pat_params: & self.hir(impl_.0).impl_(impl_.1).ty_params,
            pat_vars: Vec::new(),
        };
        if self.match_type0(ty, pat, &mut ctx) {
            Some(ctx.pat_vars)
        } else {
            None
        }
    }

    fn match_type0(&self, ty: TypeId, pat: TypeId, ctx: &mut MatchTypeCtx) -> bool {
        if ty == pat {
            return true;
        }

        match (&self.type_(ty).data, &self.type_(pat).data) {
            (TypeData::GenericEnv(ty_genv), TypeData::GenericEnv(pat_genv)) => {
                self.match_generic_env(ty_genv, pat_genv, ctx)
            }
            (_, &TypeData::Var(Var::Param(id))) => {
                self.match_type_param(ty, pat, id, ctx)
            }
            (TypeData::Struct(ty), TypeData::Struct(pat)) => {
                self.match_struct_type(ty, pat, ctx)
            }
            (TypeData::Fn(ty), TypeData::Fn(pat)) => {
                self.match_fn_type(ty, pat, ctx)
            }
            (TypeData::Var(Var::Inference(_)), _) => {
                self.can_unify_inference_var(ty, pat)
            }
            (_, _) => false,
        }
    }

    fn match_generic_env(&self, ty: &GenericEnv, pat: &GenericEnv, ctx: &mut MatchTypeCtx) -> bool {
        if !self.match_type0(ty.ty, pat.ty, ctx) {
            return false;
        }
        debug_assert_eq!(ty.vars.vars().collect::<Vec<_>>(), pat.vars.vars().collect::<Vec<_>>());
        for (ty, pat) in ty.vars.vals().zip(pat.vars.vals()) {
            if !self.match_type0(ty, pat, ctx) {
                return false;
            }
        }
        true
    }

    fn match_type_param(&self, ty: TypeId, pat: TypeId, param: GlobalNodeId, ctx: &mut MatchTypeCtx) -> bool {
        if param.0 == ctx.pat_package_id && ctx.pat_params.contains(&param.1) {
            ctx.pat_vars.push((pat, ty));
            true
        } else {
            false
        }
    }

    fn match_struct_type(&self, ty: &StructType, pat: &StructType, ctx: &mut MatchTypeCtx) -> bool {
        if ty.name.is_some() || pat.name.is_some() {
            ty.name == pat.name
        } else if ty.fields.len() == pat.fields.len() {
            let mut ok = true;
            for (StructTypeField { name, ty },
                StructTypeField { name: pat_name, ty: pat_ty })
                in ty.fields.iter().zip(pat.fields.iter())
            {
                if name != pat_name || !self.match_type0(*ty, *pat_ty, ctx) {
                    ok = false;
                    break;
                }
            }
            ok
        } else {
            false
        }
    }

    fn match_fn_type(&self, ty: &FnType, pat: &FnType, ctx: &mut MatchTypeCtx) -> bool {
        if ty.name.is_some() || pat.name.is_some() {
            ty.name == pat.name
        } else if ty.params.len() == pat.params.len() {
            for (&ty, &pat) in ty.params.iter().zip(pat.params.iter()) {
                if !self.match_type0(ty, pat, ctx) {
                    return false;
                }
            }
            self.match_type0(ty.result, pat.result, ctx)
        } else {
            false
        }
    }
}