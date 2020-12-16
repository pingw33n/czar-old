use super::*;

impl PassImpl<'_> {
    pub fn check_unary_op(&mut self, op: UnaryOp, node: NodeId) -> Result<TypeId> {
        let UnaryOp { kind, arg } = op;
        let arg_ty = self.typing(arg)?;
        let arg_ty = self.normalize(arg_ty);
        use UnaryOpKind::*;
        let ty = match kind.value {
            Deref => {
                self.check_data.set_lvalue(node);
                if self.as_primitive(arg_ty) == Some(PrimitiveType::Ptr) {
                    self.type_(arg_ty).data.as_generic_env().unwrap().vars.vals().next().unwrap()
                } else {
                    self.err_unary_op_not_defined(node, kind, arg_ty);
                    return Err(());
                }
            }
            Neg => {
                let ok =
                    // Any number.
                    self.as_any_number(arg_ty).is_some();
                if !ok {
                    self.err_unary_op_not_defined(node, kind, arg_ty);
                    return Err(());
                }
                arg_ty
            }
            _ => todo!(),
        };
        Ok(ty)
    }

    fn err_unary_op_not_defined(&self, node: NodeId, kind: S<UnaryOpKind>, arg_ty: TypeId) {
        self.error_span(node, kind.span, format!(
            "unary operation `{}` can't be applied to type `{}`",
            kind.value, self.display_type(arg_ty)));
    }
}