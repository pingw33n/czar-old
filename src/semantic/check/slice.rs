use std::convert::TryFrom;

use super::*;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct SliceType {
    pub item: TypeId,
    pub len: Option<u32>,
}

impl PassImpl<'_> {
    pub fn check_slice_literal(&mut self, node: NodeId) -> Result<TypeId> {
        let SliceLiteral { items, len } = self.hir.slice_literal(node);

        let item_ty = self.check_items(node, items);

        let const_len = if let Some(len_val) = len.value {
            let ty = self.typing(len_val)?;
            let expected = self.std().type_(LangItem::Primitive(PrimitiveType::USize));
            self.unify(ty, expected);
            if self.normalize(ty) != self.normalize(expected) {
                self.error(len_val, format!("invalid type of slice literal length: expected `usize`, found `{}`",
                    self.display_type(ty)));
                return Err(());
            }

            if len.const_ {
                Some(self.eval_slice_len(len_val)?)
            } else {
                None
            }
        } else if len.const_ {
            Some(u32::try_from(items.len()).unwrap())
        } else {
            None
        };

        let ty = self.make_slice_type(node, item_ty?, const_len);

        Ok(ty)
    }

    pub fn check_slice_type(&mut self, node: NodeId, ty: &hir::SliceType) -> Result<TypeId> {
        let &hir::SliceType { item_ty, len } = ty;
        let item_ty = self.typing(item_ty)?;
        let len = if let Some(len) = len {
            Some(self.eval_slice_len(len)?)
        } else {
            None
        };
        Ok(self.make_slice_type(node, item_ty, len))
    }

    pub fn check_slice_index_op(&mut self, node: NodeId /*Op*/, slice_ty: TypeId, index_arg_ty: TypeId) -> Result<TypeId> {
        let slice_ty = self.normalize(slice_ty);
        let index_ty = self.normalize(index_arg_ty);
        let lang_item = self.as_lang_item(index_ty);
        let (name, lvalue_result) = if matches!(self.as_any_number(index_ty), Some(NumberKind::Int)) {
            self.unify(index_ty, self.std().type_(LangItem::Primitive(PrimitiveType::USize)));
            if !matches!(self.as_lang_item(index_ty), Some(LangItem::Primitive(PrimitiveType::USize))) {
                self.err_cant_index_slice(node, slice_ty, index_ty);
                return Err(())
            }
            self.check_data.set_lvalue(node);
            ("__index_usize", true)
        } else if matches!(lang_item, Some(LangItem::Range(_))) {
            let range_item_ty = self.type_(index_ty).data.as_generic_env().unwrap().vars.vals().next();
            if let Some(range_item_ty) = range_item_ty {
                if matches!(self.as_any_number(range_item_ty), Some(NumberKind::Int)) {
                    self.unify(range_item_ty, self.std().type_(LangItem::Primitive(PrimitiveType::USize)));
                }
                if !matches!(self.as_primitive(range_item_ty), Some(PrimitiveType::USize)) {
                    self.err_cant_index_slice(node, slice_ty, index_ty);
                    return Err(())
                }
            }
            (match lang_item.unwrap().into_range().unwrap() {
                RangeItem::Range => "__index_range",
                RangeItem::RangeFrom => "__index_range_from",
                RangeItem::RangeFull => "__index_range_full",
                RangeItem::RangeInclusive => "__index_range_inclusive",
                RangeItem::RangeTo => "__index_range_to",
                RangeItem::RangeToInclusive => "__index_range_to_inclusive",
            }, false)
        } else {
            self.err_cant_index_slice(node, slice_ty, index_ty);
            return Err(());
        };

        let name = self.hir.node_kind(node).span.spanned(Ident::from(name));
        let (fn_def, callee_ty) = self.check_method_call_manual(node, slice_ty, PathItem {
                node,
                name,
                ty_args: None,
            }, &FnParamsSignature::from_idents(&["self", "_"])).unwrap();

        assert!(self.check_data.op_impls.insert(node, OpImpl {
                fn_def,
                callee_ty,
                lvalue_result,
            }).is_none());

        let callee_ty = self.normalize(callee_ty);
        let res_ty = self.underlying_type(callee_ty).data.as_fn().unwrap().result;
        let res_ty = if lvalue_result {
            debug_assert_eq!(self.as_lang_item(res_ty), Some(LangItem::Ptr));
            self.type_(res_ty).data.as_generic_env().unwrap().vars.vals().next().unwrap()
        } else {
            res_ty
        };
        Ok(res_ty)
    }

    fn make_slice_type(&mut self, node: NodeId, item: TypeId, len: Option<u32>) -> TypeId {
        self.insert_type((self.package_id, node), TypeData::Slice(SliceType {
            item,
            len,
        }))
    }

    fn check_items(&mut self, node: NodeId, items: &[NodeId]) -> Result<TypeId> {
        let expected = if let Some(&n) = items.first() {
            self.typing(n)?
        } else {
            return Ok(self.new_inference_var(node, InferenceVar::Any));
        };
        for &item in items.iter().skip(1) {
            let ty = self.typing(item)?;
            self.unify(expected, ty);
            if ty != expected {
                if self.normalize(expected) != self.normalize(ty) {
                    self.error(item, format!("mismatching types of slice literal items: expected `{}`, found `{}`",
                        self.display_type(expected),
                        self.display_type(ty)));
                    return Err(());
                }
            }
        }
        Ok(expected)
    }

    fn eval_slice_len(&self, len: NodeId) -> Result<u32> {
        if let Some(&Literal::Int(IntLiteral { value, ty: _ })) = self.hir.try_literal(len) {
            if value > u32::max_value() as u128 {
                todo!("const range checking");
            }
            Ok(value as u32)
        } else {
            self.error(len, format!("expected constant expression"));
            Err(())
        }
    }

    fn err_cant_index_slice(&self, node: NodeId, slice_ty: TypeId, index_ty: TypeId) {
        self.error(node, format!("type `{}` cannot be indexed by `{}`",
            self.display_type(slice_ty),
            self.display_type(index_ty)));
    }
}