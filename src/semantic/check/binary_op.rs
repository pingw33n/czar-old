use super::*;

impl PassImpl<'_> {
    pub fn check_binary_op(&mut self, op: BinaryOp, node: NodeId) -> Result<TypeId> {
        let BinaryOp { kind, left, right } = op;
        let left_ty = self.typing(left)?;
        let right_ty = self.typing(right)?;
        self.unify(left_ty, right_ty);
        let left_ty = self.normalize(left_ty);
        let right_ty = self.normalize(right_ty);

        use BinaryOpKind::*;
        let ty = match kind.value {
            Assign => {
                if !self.check_data.is_lvalue(left) {
                    self.error(left, "can't assign to this expression".into());
                } else {
                    if left_ty != right_ty {
                        self.error(right, format!(
                            "mismatching types: expected `{}`, found `{}`",
                            self.display_type(left_ty),
                            self.display_type(right_ty)));
                    }
                }
                self.std().unit_type()
            }
            | Eq
            | Gt
            | GtEq
            | Lt
            | LtEq
            | NotEq
            => {
                let lli = self.as_lang_item(left_ty);
                let rli = self.as_lang_item(right_ty);
                let ok =
                    // Any primitive.
                    matches!((lli, rli), (Some(LangItem::Primitive(l)), Some(LangItem::Primitive(r))) if l == r)
                    // Unit
                    || self.is_unit_type(left_ty) && self.is_unit_type(right_ty)
                    // String
                    || matches!(lli, Some(LangItem::String)) && lli == rli
                    // Any number.
                    || matches!((self.as_any_number(left_ty), self.as_any_number(right_ty)),
                        (Some(l), Some(r)) if l == r);
                if !ok {
                    self.err_binary_op_not_defined(node, kind, left_ty, right_ty);
                }
                self.std().type_(LangItem::Primitive(PrimitiveType::Bool))
            },
            | Add
            | Div
            | Mul
            | Sub
            | Rem
            => {
                let mut ok =
                    // Any number.
                    matches!((self.as_any_number(left_ty), self.as_any_number(right_ty)),
                        (Some(l), Some(r)) if l == r);
                if !ok {
                    // Ptr {+|-} usize
                    ok = matches!(kind.value, Add | Sub)
                        && matches!(self.as_lang_item(left_ty), Some(LangItem::Ptr))
                        && matches!(self.as_any_number(right_ty), Some(NumberKind::Int));
                    if ok {
                        self.unify(right_ty, self.std().type_(LangItem::Primitive(PrimitiveType::ISize)));
                        let right_ty = self.normalize(right_ty);
                        if self.as_primitive(right_ty) != Some(PrimitiveType::ISize) {
                            self.error(right, format!(
                                "mismatching types: expected `isize`, found `{}`",
                                self.display_type(right_ty)));
                        }
                    }
                }
                if !ok {
                    self.err_binary_op_not_defined(node, kind, left_ty, right_ty);
                    return Err(());
                }
                left_ty
            }
            Index => {
                let left_ty = self.normalize(left_ty);
                if self.underlying_type(left_ty).data.as_slice().is_some() {
                    self.check_slice_index_op(node, left_ty, right_ty)?
                } else {
                    self.error(node, format!("index operation is not defined for type `{}`",
                        self.display_type(left_ty)));
                    return Err(());
                }
            }
            _ => todo!("{:?}", kind),
        };
        Ok(ty)
    }

    fn err_binary_op_not_defined(&self, node: NodeId, kind: S<BinaryOpKind>, left_ty: TypeId, right_ty: TypeId) {
        self.error_span(node, kind.span, format!(
            "binary operation `{}` can't be applied to types `{}`, `{}`",
            kind.value,
            self.display_type(left_ty),
            self.display_type(right_ty)));
    }
}