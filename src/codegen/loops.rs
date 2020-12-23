use super::*;

#[derive(Clone, Copy)]
pub struct Loop {
    pub break_bb: BasicBlockRef,
    pub continue_bb: BasicBlockRef,
}

impl ExprCtx<'_> {
    pub fn with_loop<F, R>(&mut self, node: NodeId, loop_: Loop, f: F) -> R
        where F: FnOnce(&mut Self) -> R
    {
        assert!(self.loops.insert(node, loop_).is_none());

        let r = f(self);

        self.loops.remove(&node).unwrap();

        r
    }
}

impl Codegen<'_> {
    pub fn while_(&mut self, node: NodeId /*While*/, ctx: &mut ExprCtx) -> Result<Value> {
        let &While { cond, body } = ctx.package.hir.while_(node);

        let cond_bb = self.llvm.append_new_bb(ctx.fn_, "__while_cond");
        let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__while_succ");

        ctx.with_loop(node, Loop {
            break_bb: succ_bb,
            continue_bb: cond_bb,
        }, move |ctx| {
            let wbody_bb = self.llvm.append_new_bb(ctx.fn_, "__while_body");

            self.bodyb.br(cond_bb);

            self.bodyb.position_at_end(cond_bb);
            let cond = if let Ok(v) = self.expr(cond, ctx) {
                v.deref(self.bodyb)
            } else {
                self.bodyb.position_at_end(succ_bb);
                self.bodyb.unreachable();
                self.bodyb.position_at_end(wbody_bb);
                self.bodyb.unreachable();
                self.bodyb.position_at_end(cond_bb);

                return Err(());
            };

            self.bodyb.cond_br(cond, wbody_bb, succ_bb);

            self.bodyb.position_at_end(wbody_bb);
            if self.expr(body, ctx).is_ok() {
                self.bodyb.br(cond_bb);
            }

            self.bodyb.position_at_end(succ_bb);

            Ok(self.unit_literal().into())
        })
    }
}