mod fns;
mod llvm;
mod types;

use std::collections::{hash_map, HashMap};

use crate::hir::*;
use crate::package::{Package, Packages, GlobalNodeId, PackageId};
use crate::semantic::check::{self, *};
use crate::syntax::*;

use fns::*;
use llvm::*;
use types::{*, GenericEnv};

pub use llvm::OutputFormat;

pub struct ExprCtx<'a> {
    package: &'a Package,
    fn_: ValueRef,
    allocas: &'a mut NodeMap<Value>,
    genv: &'a GenericEnv,
}

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Direct(ValueRef),
    Indirect(ValueRef),
}

impl Value {
    fn ptr(self) -> ValueRef {
        match self {
            Self::Direct(v) => v,
            Self::Indirect(v) => v,
        }
    }

    fn deref(self, b: BuilderRef) -> ValueRef {
        match self {
            Self::Direct(v) => v,
            Self::Indirect(v) => b.load(v),
        }
    }
}

trait FromValueRef {
    fn direct(self) -> Value;
    fn indirect(self) -> Value;
}

impl FromValueRef for ValueRef {
    fn direct(self) -> Value {
        Value::Direct(self)
    }

    fn indirect(self) -> Value {
        Value::Indirect(self)
    }
}

pub struct Codegen<'a> {
    llvm: Llvm,
    bodyb: BuilderRef,
    last_alloca: Option<ValueRef>,
    packages: &'a Packages,
    fn_decls: HashMap<TopLevelMonoId, ValueRef>,
    fn_mono_reqs: HashMap<TopLevelMonoId, FnMonoRequest>,
    types: HashMap<MonoId, TypeLl>,
    defined_types: HashMap<TopLevelMonoId, TypeRef>,
}

impl<'a> Codegen<'a> {
    pub fn new(packages: &'a Packages) -> Self {
        let mut llvm = Llvm::new();
        let bodyb = llvm.new_builder();
        Self {
            llvm,
            bodyb,
            last_alloca: None,
            packages,
            fn_decls: HashMap::new(),
            fn_mono_reqs: HashMap::new(),
            types: HashMap::new(),
            defined_types: HashMap::new(),
        }
    }

    pub fn lower(&mut self, package_id: PackageId) {
        let entry_point = self.packages[package_id].check_data.entry_point().unwrap();
        let node = self.packages.underlying_type(entry_point).data.name().unwrap();

        self.fn_def(node, entry_point, &self.default_genv()).unwrap();

        while let Some(&fnid) = self.fn_mono_reqs.keys().next() {
            let req = self.fn_mono_reqs.remove(&fnid).unwrap();
            self.mono_fn(fnid, req);
        }
    }

    pub fn emit(&self, out: &mut impl std::io::Write, format: OutputFormat) -> std::io::Result<()> {
        self.llvm.emit(out, format)
    }

    pub fn emit_to_file(&self, path: impl AsRef<std::path::Path>, format: OutputFormat) -> std::io::Result<()> {
        let file = &mut std::fs::File::create(path)?;
        self.emit(file, format)
    }

    fn make_ptr(&mut self, v: Value, ctx: &mut ExprCtx) -> ValueRef {
        match v {
            Value::Direct(v) => {
                let tmp = self.alloca_new_ty(v.type_(), "", ctx).ptr();
                self.bodyb.store(v, tmp);
                tmp
            }
            Value::Indirect(v) => v,
        }
    }

    fn expr(&mut self, node: NodeId, ctx: &mut ExprCtx) -> Result<Value> {
        Ok(match ctx.package.hir.node_kind(node).value {
            NodeKind::Block => {
                let Block { exprs } = ctx.package.hir.block(node);
                let mut r = None;
                for &expr in exprs {
                    r = Some(self.expr(expr, ctx)?);

                }
                r.unwrap_or_else(|| self.unit_literal().into())
            }
            NodeKind::FieldAccess => {
                let receiver = ctx.package.hir.field_access(node).receiver;
                let receiver = self.expr(receiver, ctx)?;
                let receiver = self.make_ptr(receiver, ctx).into();
                let idx = ctx.package.check_data.struct_field_index(node);
                self.bodyb.struct_gep(receiver, idx).indirect()
            }
            NodeKind::FnCall => {
                let fnc = ctx.package.hir.fn_call(node);
                let mut args = Vec::new();
                for arg in &fnc.args {
                    args.push(self.expr(arg.value, ctx)?);
                }
                let callee_ty = ctx.package.check_data.typing(fnc.callee);
                let callee = self.expr(fnc.callee, ctx)?;
                self.fn_call(Some(node), callee_ty, callee, &args, ctx)?
            }
            NodeKind::IfExpr => {
                let fn_ = ctx.fn_;

                let &IfExpr { cond, if_true, if_false } = ctx.package.hir.if_expr(node);
                let cond = self.expr(cond, ctx)?.deref(self.bodyb);

                let if_true_bb = self.llvm.append_new_bb(fn_, "__if_true");
                let if_false_bb = self.llvm.append_new_bb(fn_, "__if_false");
                let succ_bb = self.llvm.append_new_bb(fn_, "__if_succ");

                self.bodyb.cond_br(cond, if_true_bb, if_false_bb);

                let ret_var = if if_false.is_some() {
                    Some(self.alloca(node, "__if", ctx).ptr())
                } else {
                    None
                };

                self.bodyb.position_at_end(if_true_bb);
                let if_true_diverges = if let Ok(v) = self.expr(if_true, ctx) {
                    if let Some(ret_var) = ret_var {
                        self.bodyb.store(v.deref(self.bodyb), ret_var);
                    }
                    self.bodyb.br(succ_bb);
                    false
                } else {
                    true
                };

                self.bodyb.position_at_end(if_false_bb);
                let if_false_diverges = if let Some(if_false) = if_false {
                    if let Ok(v) = self.expr(if_false, ctx) {
                        self.bodyb.store(v.deref(self.bodyb), ret_var.unwrap());
                        false
                    } else {
                        true
                    }
                } else {
                    false
                };
                if !if_false_diverges {
                    self.bodyb.br(succ_bb);
                }

                self.bodyb.position_at_end(succ_bb);

                if if_true_diverges && if_false_diverges {
                    self.bodyb.unreachable();
                    return Err(());
                }

                if let Some(ret_var) = ret_var {
                    ret_var.indirect()
                } else {
                    self.unit_literal()
                }
            }
            NodeKind::FnDefParam => ctx.allocas[&node].into(),
            NodeKind::Let => {
                let &Let { def } = ctx.package.hir.let_(node);

                let &LetDef { init, .. } = ctx.package.hir.let_def(def);
                if let Some(init) = init {
                    let var = self.expr(def, ctx)?.ptr();
                    let val = self.expr(init, ctx)?.deref(self.bodyb);
                    self.bodyb.store(val, var);
                    self.bool_literal(true)
                } else {
                    self.unit_literal()
                }
            }
            NodeKind::LetDef => {
                let name = ctx.package.hir.let_def(node).name.value.as_str();
                self.alloca(node, name, ctx)
            }
            NodeKind::Literal => {
                let lit = ctx.package.hir.literal(node);
                match lit {
                    &Literal::Bool(v) => self.bool_literal(v),
                    &Literal::Char(v) => self.char_literal(v),
                    Literal::String(v) => self.string_literal(v),
                    &Literal::Int(IntLiteral { value, .. }) => {
                        let ty = self.typing((ctx.package.id, node), ctx.genv)?;
                        ty.const_int(value).direct()
                    },
                    &Literal::Float(FloatLiteral { value, .. }) => {
                        let ty = self.typing((ctx.package.id, node), ctx.genv)?;
                        ty.const_real(value).direct()
                    },
                    Literal::Unit => self.unit_literal(),
                }.into()
            }
            NodeKind::Op => {
                if let Some(OpImpl { fn_def, callee_ty, lvalue_result }) = ctx.package.check_data.op_impl(node) {
                    let callee = self.fn_def(fn_def, callee_ty, ctx.genv)?;
                    let r = match ctx.package.hir.op(node) {
                        &Op::Binary(BinaryOp { kind: _, left, right }) => {
                            let left = self.expr(left, ctx)?;
                            let right = self.expr(right, ctx)?;
                            self.fn_call(Some(node), callee_ty, callee, &[left, right], ctx)?
                        }
                        &Op::Unary(UnaryOp { kind: _, arg }) => {
                            let arg = self.expr(arg, ctx)?;
                            self.fn_call(Some(node), callee_ty, callee, &[arg], ctx)?
                        }
                    };
                    if lvalue_result {
                        r.ptr().indirect()
                    } else {
                        r
                    }
                } else {
                    let op = ctx.package.hir.op(node);
                    match op {
                        &Op::Binary(BinaryOp { kind, left, right }) => {
                            let leftv = self.expr(left, ctx)?;
                            let rightv = self.expr(right, ctx)?.deref(self.bodyb);
                            let left_ty = self.packages.typing((ctx.package.id, left));
                            use BinaryOpKind::*;
                            if kind.value == Assign {
                                self.bodyb.store(rightv, leftv.ptr());
                                self.unit_literal()
                            } else {
                                let leftv = leftv.deref(self.bodyb);
                                match kind.value {
                                    Add | Sub => {
                                        if let Some(num) = self.packages.as_number(left_ty) {
                                            match kind.value {
                                                Add => match num {
                                                    NumberType::Float => self.bodyb.fadd(leftv, rightv),
                                                    NumberType::Int { signed: _ } => self.bodyb.add(leftv, rightv),
                                                }
                                                Sub => match num {
                                                    NumberType::Float => self.bodyb.fsub(leftv, rightv),
                                                    NumberType::Int { signed: _ } => self.bodyb.sub(leftv, rightv),
                                                }
                                                _ => unreachable!(),
                                            }
                                        } else {
                                            assert_eq!(self.packages.as_primitive(left_ty), Some(PrimitiveType::Ptr));
                                            let rightv = if kind.value == BinaryOpKind::Sub {
                                                self.bodyb.neg(rightv)
                                            } else {
                                                rightv
                                            };
                                            self.bodyb.gep_in_bounds(leftv, &mut [rightv])
                                        }.direct()
                                    },
                                    Assign => unreachable!(),
                                    | Eq
                                    | Gt
                                    | GtEq
                                    | Lt
                                    | LtEq
                                    | NotEq => {
                                        if self.packages.is_unit(left_ty) {
                                            self.bool_literal(true)
                                        } else {
                                            match self.packages.as_number(left_ty).expect("todo") {
                                                NumberType::Float => {
                                                    use RealPredicate::*;
                                                    let pred = match kind.value {
                                                        Eq => LLVMRealOEQ,
                                                        Gt => LLVMRealOGT,
                                                        GtEq => LLVMRealOGE,
                                                        Lt => LLVMRealOLT,
                                                        LtEq => LLVMRealOLE,
                                                        NotEq => LLVMRealONE,
                                                        _ => unreachable!(),
                                                    };
                                                    self.bodyb.fcmp(leftv, rightv, pred)
                                                }
                                                NumberType::Int { signed } => {
                                                    use IntPredicate::*;
                                                    let pred = match kind.value {
                                                        Eq => LLVMIntEQ,
                                                        Gt => if signed { LLVMIntSGT } else { LLVMIntUGT },
                                                        GtEq => if signed { LLVMIntSGE } else { LLVMIntUGE },
                                                        Lt => if signed { LLVMIntSLT } else { LLVMIntULT },
                                                        LtEq => if signed { LLVMIntSLE } else { LLVMIntULE },
                                                        NotEq => LLVMIntNE,
                                                        _ => unreachable!(),
                                                    };
                                                    self.bodyb.icmp(leftv, rightv, pred)
                                                }
                                            }.direct()
                                        }
                                    },
                                    Mul => {
                                        match self.packages.as_number(left_ty).expect("todo") {
                                            NumberType::Float => self.bodyb.fmul(leftv, rightv),
                                            NumberType::Int { signed: _ } => self.bodyb.mul(leftv, rightv),
                                        }.direct()
                                    },
                                    Div => {
                                        self.div_or_rem(leftv, left_ty, rightv, true, ctx)
                                    },
                                    Rem => {
                                        self.div_or_rem(leftv, left_ty, rightv, false, ctx)
                                    },
                                    Index => unreachable!(),

                                    _ => todo!("{:?}", kind)
                                }
                            }
                        },
                        &Op::Unary(UnaryOp { kind, arg }) => {
                            let argv = self.expr(arg, ctx)?.deref(self.bodyb);
                            let arg_ty = self.packages.typing((ctx.package.id, arg));
                            use UnaryOpKind::*;
                            match kind.value {
                                Deref => {
                                    assert_eq!(self.packages.as_primitive(arg_ty), Some(PrimitiveType::Ptr));
                                    argv.indirect()
                                }
                                Neg => {
                                    match self.packages.as_number(arg_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fneg(argv),
                                        NumberType::Int { signed: _ } => self.bodyb.neg(argv),
                                    }.direct()
                                }
                                _ => todo!("{:?}", kind)
                            }
                        },
                    }
                }
            }
            NodeKind::Path => {
                let reso = ctx.package.check_data.target_of(node);
                let package = &self.packages[reso.0];
                if package.hir.node_kind(reso.1).value == NodeKind::FnDef {
                    self.fn_def(reso, ctx.package.check_data.typing(node), ctx.genv)?
                } else {
                    self.expr(reso.1, &mut ExprCtx {
                        package,
                        fn_: ctx.fn_,
                        allocas: ctx.allocas,
                        genv: ctx.genv,
                    })?
                }
            }
            NodeKind::Range => {
                let &Range { kind: _, start, end } = ctx.package.hir.range(node);

                let mut idx = 0;
                let mut struct_var = None;
                for &v in &[start, end] {
                    let v = if let Some(v) = v {
                        Some(self.expr(v, ctx)?.deref(self.bodyb))
                    } else {
                        None
                    };
                    struct_var = Some(self.alloca(node, "range_literal", ctx));
                    if let Some(v) = v {
                        let ptr = self.bodyb.struct_gep(struct_var.unwrap().ptr(), idx);
                        self.bodyb.store(v, ptr);
                        idx += 1;
                    }
                }

                struct_var.unwrap()
            }
            NodeKind::SliceLiteral => {
                let ty = self.normalized(self.packages.typing((ctx.package.id, node)));
                let ty = self.packages.type_(ty).data.as_slice().unwrap();

                let SliceLiteral { items, len } = ctx.package.hir.slice_literal(node);
                let len_val = if let Some(v) = len.value {
                    if len.const_ {
                        self.llvm.size_type().const_int(ty.len.unwrap() as u128)
                    } else {
                        assert_eq!(items.len(), 1);
                        self.expr(v, ctx)?.deref(self.bodyb)
                    }
                } else {
                    self.llvm.size_type().const_int(items.len() as u128)
                };

                let item_ty = self.type_(ty.item, ctx.genv)?;

                let slice_var = self.alloca(node, "slice_literal", ctx).ptr();

                let ptr = if len.const_ {
                    self.bodyb.bitcast(slice_var, self.llvm.pointer_type(item_ty))
                } else {
                    let ptr = self.gc_malloc(item_ty, len_val, node, ctx);
                    self.bodyb.store(ptr, self.bodyb.struct_gep(slice_var, 0));
                    self.bodyb.store(len_val, self.bodyb.struct_gep(slice_var, 1));
                    ptr
                };

                if len.value.is_some() {
                    let item_val = self.expr(items[0], ctx)?.deref(self.bodyb);

                    let cond_bb = self.llvm.append_new_bb(ctx.fn_, "__slice_init_cond");
                    let block_bb = self.llvm.append_new_bb(ctx.fn_, "__slice_init_block");
                    let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__slice_init_succ");

                    let idx = self.alloca_new_ty(self.llvm.size_type(), "__slice_init_idx", ctx).ptr();
                    self.bodyb.store(self.llvm.size_type().const_int(0), idx);
                    self.bodyb.br(cond_bb);

                    self.bodyb.position_at_end(cond_bb);
                    let idx_val = self.bodyb.load(idx);
                    let cond = self.bodyb.icmp(idx_val, len_val, IntPredicate::LLVMIntULT);
                    self.bodyb.cond_br(cond, block_bb, succ_bb);

                    self.bodyb.position_at_end(block_bb);
                    let item_ptr = self.bodyb.gep_in_bounds(ptr.into(), &mut [idx_val]);
                    self.bodyb.store(item_val, item_ptr);

                    let idx_val = self.bodyb.add(idx_val, self.llvm.size_type().const_int(1));
                    self.bodyb.store(idx_val, idx);

                    self.bodyb.br(cond_bb);

                    self.bodyb.position_at_end(succ_bb);
                } else {
                    for (i, &item) in items.iter().enumerate() {
                        let item_val = self.expr(item, ctx)?.deref(self.bodyb);
                        let item_ptr = self.bodyb.gep_in_bounds(ptr.into(), &mut [
                            self.llvm.int_type(32).const_int(i as u128),
                        ]);
                        self.bodyb.store(item_val, item_ptr);
                    }
                }

                slice_var.indirect()
            }
            NodeKind::StructLiteral => {
                let StructLiteral { fields, .. } = ctx.package.hir.struct_literal(node);
                if fields.is_empty() {
                    let ty = ctx.package.check_data.typing(node);
                    let ty = self.type_(ty, ctx.genv)?;
                    ty.const_struct(&mut []).direct()
                } else {
                    let mut struct_var = None;
                    for &field in fields {
                        let value = ctx.package.hir.struct_literal_field(field).value;
                        let field_val = self.expr(value, ctx)?.deref(self.bodyb);
                        let idx = ctx.package.check_data.struct_field_index(field);
                        struct_var = Some(self.alloca(node, "struct_literal", ctx));
                        let field_ptr = self.bodyb.struct_gep(struct_var.unwrap().ptr(), idx);
                        self.bodyb.store(field_val, field_ptr);
                    }
                    struct_var.unwrap().into()
                }
            }
            NodeKind::StructLiteralField => unreachable!(),
            NodeKind::While => {
                let &While { cond, body } = ctx.package.hir.while_(node);

                let cond_bb = self.llvm.append_new_bb(ctx.fn_, "__while_cond");
                self.bodyb.br(cond_bb);

                self.bodyb.position_at_end(cond_bb);
                let cond = self.expr(cond, ctx)?.deref(self.bodyb);

                let wbody_bb = self.llvm.append_new_bb(ctx.fn_, "__while_body");
                let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__while_succ");
                self.bodyb.cond_br(cond, wbody_bb, succ_bb);

                self.bodyb.position_at_end(wbody_bb);
                if self.expr(body, ctx).is_ok() {
                    self.bodyb.br(cond_bb);
                }

                self.bodyb.position_at_end(succ_bb);

                self.unit_literal().into()
            }
            // FnDef here is only reachable directly.
            // Indirect case is handled within the Path case.
            | NodeKind::FnDef
            | NodeKind::Impl
            | NodeKind::Module
            | NodeKind::Struct
            | NodeKind::TypeAlias
            | NodeKind::Use
            => {
                self.unit_literal().into()
            }
            _ => todo!("{:?}", ctx.package.hir.node_kind(node))
        })
    }

    fn div_or_rem(&mut self,
        leftv: ValueRef,
        left_ty: TypeId,
        rightv: ValueRef,
        div: bool,
        ctx: &mut ExprCtx,
    ) -> Value {
        match self.packages.as_number(left_ty).expect("todo") {
            NumberType::Float => if div {
                self.bodyb.fdiv(leftv, rightv)
            } else {
                self.bodyb.frem(leftv, rightv)
            }
            NumberType::Int { signed } => {
                let cond = self.bodyb.icmp(rightv, rightv.type_().const_int(0), IntPredicate::LLVMIntEQ);
                self.panic_if(cond, "integer division by zero", ctx);
                if signed {
                    if div {
                        self.bodyb.sdiv(leftv, rightv)
                    } else {
                        self.bodyb.srem(leftv, rightv)
                    }
                } else {
                    if div {
                        self.bodyb.udiv(leftv, rightv)
                    } else {
                        self.bodyb.urem(leftv, rightv)
                    }
                }
            },
        }.direct()
    }

    fn panic_if(&mut self, cond: ValueRef, msg: &str, ctx: &mut ExprCtx) {
        let panic_bb = self.llvm.append_new_bb(ctx.fn_, "__panic");
        let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__panic_succ");
        self.bodyb.cond_br(cond, panic_bb, succ_bb);

        self.bodyb.position_at_end(panic_bb);
        self.panic(msg, ctx);

        self.bodyb.position_at_end(succ_bb);
    }

    fn panic(&mut self, msg: &str, ctx: &mut ExprCtx) {
        let callee_ty = self.packages.std().check_data.lang().type_(
            LangItem::Intrinsic(IntrinsicItem::Panic));
        let fn_def = self.packages.underlying_type(callee_ty).data.name().unwrap();
        let callee = self.fn_def(fn_def, callee_ty, ctx.genv).unwrap();
        let msg = self.string_literal(msg);
        assert!(self.fn_call(None, callee_ty, callee, &[msg], ctx).is_err());
    }

    fn bool_literal(&mut self, v: bool) -> Value {
        let v = if v { 1 } else { 0 };
        self.lang_type(LangItem::Primitive(PrimitiveType::Bool)).const_int(v).direct()
    }

    fn char_literal(&mut self, v: char) -> Value {
        self.lang_type(LangItem::Primitive(PrimitiveType::Char)).const_int(v as u128).direct()
    }

    fn string_literal(&mut self, v: &str) -> Value {
        let ptr = self.llvm.add_global_string_const(v);
        let len = self.lang_type(LangItem::Primitive(PrimitiveType::USize)).const_int(v.len() as u128);
        let ty = self.lang_type(LangItem::String);
        ty.const_struct(&mut [ptr, len]).direct()
    }

    fn unit_literal(&mut self) -> Value {
        self.type_(self.packages.std().check_data.lang().unit_type(), &self.default_genv()).unwrap()
            .const_struct(&mut [])
            .direct()
    }

    /// Returns `item_ty*`
    fn gc_malloc(&self, item_ty: TypeRef, len: ValueRef, node: NodeId, ctx: &mut ExprCtx) -> ValueRef {
        let item_size = self.llvm.size_type().const_int(self.llvm.abi_size_bytes(item_ty) as u128);
        let len_bytes = self.bodyb.mul(len, item_size);
        let file = ctx.package.hir.sources()
            [ctx.package.discover_data.source_of(node, &ctx.package.hir)]
            .path.to_string_lossy();
        let line = ctx.package.hir.node_kind(node).span.start; // FIXME
        let ptr = intrinsic::gc_debug_malloc(&self.llvm, self.bodyb, len_bytes, &file, line as u32);
        self.bodyb.bitcast(ptr, item_ty.pointer())
    }
}

impl std::fmt::Display for Codegen<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.llvm)
    }
}

impl std::fmt::Debug for Codegen<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}