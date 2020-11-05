use super::*;

impl PassImpl<'_> {
    pub fn check_unary_op(&mut self, op: UnaryOp, node: NodeId) -> Result<TypeId> {
        let UnaryOp { kind, arg } = op;
        let arg_ty = self.type_(self.typing(arg)?);
        use UnaryOpKind::*;
        let ty = match kind.value {
            Neg => {
                let ok =
                    // Any number.
                    self.as_any_number(arg_ty.id()).is_some();
                if !ok {
                    self.error_span(node, kind.span, format!(
                        "unary operation `{}` can't be applied to type `{}`",
                        kind.value, self.display_type(arg_ty.id())));
                    return Err(());
                }
                arg_ty.id()
            }
            _ => todo!(),
        };
        Ok(ty)
    }
}