use super::*;

pub type TopLevelMonoId = (GlobalNodeId, GenericEnvId);
pub type MonoId = (TypeId, GenericEnvId);

pub struct FnMonoRequest {
    pub genv_vars: TypeVarMap,
}

impl Codegen<'_> {
    pub fn fn_def(&mut self, fn_def: GlobalNodeId, callee_ty: TypeId, genv: &GenericEnv) -> Result<Value> {
        // Handle LLVM intrinsics.
        if let Some(intrinsic) = self.packages.as_lang_item(callee_ty)
            .and_then(|v| v.into_intrinsic().ok())
        {
            match intrinsic {
                IntrinsicItem::Unreachable => return Ok(self.unit_literal()),
                | IntrinsicItem::Panic
                | IntrinsicItem::Transmute
                => {},
            }
        }

        let callee_ty = self.normalized(callee_ty);

        let genv_vars = self.resolve_fn_genv_vars(callee_ty, genv);
        let genv_id = self.make_genv_id(&genv_vars, genv)?;

        let mid = (fn_def, genv_id);
        if let Some(&v) = self.fn_decls.get(&mid) {
            return Ok(v.direct());
        }

        let package = &self.packages[fn_def.0];
        let name = if package.check_data.entry_point() == Some(callee_ty) {
            "__main"
        } else {
            package.hir.fn_def(fn_def.1).name.value.as_str()
        };
        let ty = self.packages.type_(callee_ty);
        let ty_ll = self.type_(ty.id, genv)?;
        let fn_ = self.llvm.add_function(&name, ty_ll);
        assert!(self.fn_decls.insert(mid, fn_).is_none());
        assert!(self.fn_mono_reqs.insert(mid, FnMonoRequest {
            genv_vars,
        }).is_none());

        Ok(fn_.direct())
    }

    pub fn mono_fn(&mut self, id: TopLevelMonoId, req: FnMonoRequest) {
        let fn_def = id.0;
        let package = &self.packages[fn_def.0];
        let FnDef { params, body, .. } = package.hir.fn_def(fn_def.1);
        if let Some(body) = *body {
            let fn_ = self.fn_decls[&id];
            let allocas = &mut HashMap::new();
            let ctx = &mut ExprCtx {
                package,
                fn_,
                allocas,
                genv: &GenericEnv {
                    id: id.1,
                    vars: req.genv_vars,
                },
            };

            let entry_bb = self.llvm.append_new_bb(fn_, "entry");
            self.bodyb.position_at_end(entry_bb);
            self.last_alloca = None;

            for (i, &param) in params.iter().enumerate() {
                let name = &package.hir.fn_def_param(param).name.value;
                let val = self.alloca(param, name, ctx);
                let param = fn_.param(i as u32);
                self.bodyb.store(param, val.ptr());
            }

            if let Ok(ret) = self.expr(body, ctx) {
                let ret = ret.deref(self.bodyb);
                self.bodyb.ret(ret);
            }
        }
    }

    pub fn fn_call(&mut self,
        callee_node: Option<NodeId>,
        callee_ty: TypeId,
        callee: Value,
        args: &[Value],
        ctx: &mut ExprCtx,
    ) -> Result<Value> {
        let callee_ty = self.normalized(callee_ty);
        let intrinsic = self.packages.as_lang_item(callee_ty)
            .and_then(|v| v.into_intrinsic().ok());
        let intrinsic = if let Some(intr) = intrinsic {
            match intr {
                IntrinsicItem::Panic => None,
                IntrinsicItem::Transmute => {
                    assert_eq!(args.len(), 1);
                    let src = args[0];
                    let src = self.make_ptr(src, ctx);
                    let src_size = self.llvm.abi_size_bytes(src.type_().inner());

                    let dst_ty = self.packages.underlying_type(callee_ty).data.as_fn().unwrap().result;
                    let dst_ty = if let Ok(v) = self.type_(dst_ty, ctx.genv) {
                        v
                    } else {
                        todo!("must fail in frontend");
                    };
                    let dst_size = self.llvm.abi_size_bytes(dst_ty);

                    if src_size != dst_size {
                        todo!("must fail in frontend");
                    }

                    let dst = self.alloca_new_ty(dst_ty, "", ctx);

                    let i8ptr = self.llvm.int_type(8).pointer();
                    let src_ptr = self.bodyb.bitcast(src, i8ptr);
                    let dst_ptr = self.bodyb.bitcast(dst.ptr(), i8ptr);
                    let len = match self.llvm.pointer_size_bits() {
                        32 => self.llvm.int_type(32),
                        64 => self.llvm.int_type(64),
                        _ => unreachable!(),
                    }.const_int(src_size as u128);
                    intrinsic::memcpy(&self.llvm, self.bodyb, dst_ptr, src_ptr, len,
                        self.llvm.int_type(1).const_int(0));

                    Some(dst)
                }
                IntrinsicItem::Unreachable => {
                    assert!(args.is_empty());
                    Some(self.unit_literal())
                }
            }
        } else {
            None
        };

        let r = if let Some(v) = intrinsic {
            v
        } else {
            let mut args = args.to_vec();
            if let Some(slice_ty) = callee_node.and_then(|v| ctx.package.check_data.method_call_self_coercion(v)) {
                // [T; N] -> [T]
                let arr = self.make_ptr(args[0], ctx);
                let arr_ty = arr.type_().inner();
                let item_ty = arr_ty.inner();
                let len = arr_ty.array_len();

                debug_assert!(matches!(self.packages.underlying_type(slice_ty).data, TypeData::Slice(_)));
                let slice_ty = self.type_(slice_ty, ctx.genv)?;

                let slice_var = self.alloca_new_ty(slice_ty, "slice_coercion", ctx).ptr();
                let ptr = self.bodyb.bitcast(arr, item_ty.pointer());
                self.bodyb.store(ptr, self.bodyb.struct_gep(slice_var, 0));
                self.bodyb.store(self.llvm.size_type().const_int(len as u128), self.bodyb.struct_gep(slice_var, 1));

                args[0] = slice_var.indirect();
            };

            let mut args: Vec<_> = args.into_iter()
                .map(|v| v.deref(self.bodyb))
                .collect();
            let callee = callee.deref(self.bodyb);
            self.bodyb.call(callee, &mut args).direct()
        };

        let ret_ty = self.packages.underlying_type(callee_ty).data.as_fn().unwrap().result;
        if self.packages.as_primitive(ret_ty) == Some(PrimitiveType::Never) {
            self.bodyb.unreachable();
            Err(())
        } else {
            Ok(r)
        }
    }

    pub fn alloca(&mut self, node: NodeId, name: &str, ctx: &mut ExprCtx) -> Value {
        if ctx.allocas.contains_key(&node) {
            ctx.allocas[&node]
        } else {
            let r = self.alloca_new(node, name, ctx);
            assert!(ctx.allocas.insert(node, r).is_none());
            r
        }
    }

    fn alloca_new(&mut self, node: NodeId, name: &str, ctx: &mut ExprCtx) -> Value {
        let ty = ctx.package.check_data.typing(node);
        let ty = self.normalized(ty);
        let ty_ll = self.type_allow_uninhabited(ty, ctx.genv);

        if let &TypeData::Slice(check::SliceType { item, len: Some(len) }) = &self.packages.underlying_type(ty).data {
            let slot_ty = ty_ll.pointer();
            let slot = self.alloca_new_ty(slot_ty, name, ctx).ptr();
            let item_ty = self.type_allow_uninhabited(item, ctx.genv);
            let ptr = self.gc_malloc(item_ty, self.llvm.size_type().const_int(len as u128), node, ctx);
            let ptr = self.bodyb.bitcast(ptr, slot_ty);
            self.bodyb.store(ptr, slot);
            ptr.indirect()
        } else {
            self.alloca_new_ty(ty_ll, name, ctx)
        }
    }

    pub fn alloca_new_ty(&mut self, ty: TypeRef, name: &str, ctx: &mut ExprCtx) -> Value {
        let cur_bb = self.bodyb.cur_bb().unwrap();
        if let Some(last_alloca) = self.last_alloca {
            self.bodyb.position_after(last_alloca);
        } else {
            self.bodyb.position_at_start(ctx.fn_.entry_bb());
        }
        let r = self.bodyb.alloca(name, ty);
        self.last_alloca = Some(r);
        self.bodyb.position_at_end(cur_bb);
        r.indirect()
    }
}