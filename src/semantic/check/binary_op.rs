use super::*;

impl PassImpl<'_> {
    pub fn check_binary_op(&mut self, op: BinaryOp, node: NodeId) -> Result<TypeId> {
        let BinaryOp { kind, left, right } = op;
        let (left_ty, right_ty) = self.unify(self.typing(left)?, self.typing(right)?);

        use BinaryOpKind::*;
        let ty = match kind.value {
            Assign => {
                if !self.check_data.is_lvalue(left) {
                    self.error(left, "can't assign to this expression".into());
                } else {
                    let left_ty = self.normalize(left_ty);
                    let right_ty = self.normalize(right_ty);
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
                let left_ty = self.type_(left_ty);
                let right_ty = self.type_(right_ty);
                let lli = self.as_lang_item(left_ty.id);
                let rli = self.as_lang_item(right_ty.id);
                let ok =
                    // Any primitive.
                    matches!((lli, rli), (Some(LangItem::Primitive(l)), Some(LangItem::Primitive(r))) if l == r)
                    // Unit
                    || self.is_unit_type(left_ty.id) && self.is_unit_type(right_ty.id)
                    // String
                    || matches!(lli, Some(v) if lli == rli && matches!(v, LangItem::String))
                    // Any number.
                    || matches!((self.as_any_number(left_ty.id), self.as_any_number(right_ty.id)),
                        (Some(l), Some(r)) if l == r);
                if !ok {
                    self.error_span(node, kind.span, format!(
                        "binary operation `{}` can't be applied to types `{}`, `{}`",
                        kind.value,
                        self.display_type(left_ty.id),
                        self.display_type(right_ty.id)));
                }
                self.std().type_(LangItem::Primitive(PrimitiveType::Bool))
            },
            | Add
            | Div
            | Mul
            | Sub
            | Rem
            => {
                let left_ty = self.type_(left_ty);
                let right_ty = self.type_(right_ty);
                let ok =
                    // Any number.
                    matches!((self.as_any_number(left_ty.id), self.as_any_number(right_ty.id)),
                        (Some(l), Some(r)) if l == r);
                if !ok {
                    self.error_span(node, kind.span, format!(
                        "binary operation `{}` can't be applied to types `{}`, `{}`",
                        kind.value,
                        self.display_type(left_ty.id),
                        self.display_type(right_ty.id)));
                    return Err(());
                }
                left_ty.id
            }
            _ => todo!("{:?}", kind),
        };
        Ok(ty)
    }
}