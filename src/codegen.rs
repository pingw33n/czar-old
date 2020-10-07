mod llvm;

use std::collections::{HashMap, HashSet};

use crate::hir::*;
use crate::package::{Package, Packages, GlobalNodeId, PackageId};
use crate::semantic::check::{self, *};
use crate::syntax::*;

use llvm::*;

pub use llvm::OutputFormat;

struct ExprCtx<'a> {
    package: &'a Package,
    fn_: llvm::DValueRef,
    allocas: &'a mut HashMap<NodeId, llvm::IValueRef>,
}

#[derive(Clone, Copy)]
enum Value {
    Direct(llvm::DValueRef),
    Indirect(llvm::IValueRef),
}

impl Value {
    fn indirect(self) -> IValueRef {
        match self {
            Self::Direct(v) => panic!("expected indirect value but found: {:?}", v),
            Self::Indirect(v) => v,
        }
    }

    fn to_direct(self, b: llvm::BuilderRef) -> DValueRef {
        match self {
            Self::Direct(v) => v,
            Self::Indirect(v) => b.load(v),
        }
    }
}

impl From<llvm::DValueRef> for Value {
    fn from(v: DValueRef) -> Self {
        Self::Direct(v)
    }
}

impl From<llvm::IValueRef> for Value {
    fn from(v: IValueRef) -> Self {
        Self::Indirect(v)
    }
}

pub struct Codegen<'a> {
    llvm: Llvm,
    bodyb: BuilderRef,
    headerb: BuilderRef,
    packages: &'a Packages,
    fn_decls: HashMap<GlobalNodeId, llvm::DValueRef>,
    fn_body_todos: HashSet<GlobalNodeId>,
    types: HashMap<TypeId, llvm::TypeRef>,
}

impl<'a> Codegen<'a> {
    pub fn new(packages: &'a Packages) -> Self {
        let mut llvm = Llvm::new();
        let bodyb = llvm.new_builder();
        let headerb = llvm.new_builder();
        Self {
            llvm,
            bodyb,
            headerb,
            packages,
            fn_decls: HashMap::new(),
            fn_body_todos: HashSet::new(),
            types: HashMap::new(),
        }
    }

    pub fn lower(&mut self, package_id: PackageId) {
        let entry_point = self.packages[package_id].resolve_data.entry_point().unwrap();

        self.fn_decl((package_id, entry_point));

        while let Some(&node) = self.fn_body_todos.iter().next() {
            self.fn_body(node);
            assert!(self.fn_body_todos.remove(&node));
        }
    }

    pub fn emit(&self, out: &mut impl std::io::Write, format: OutputFormat) -> std::io::Result<()> {
        self.llvm.emit(out, format)
    }

    pub fn emit_to_file(&self, path: impl AsRef<std::path::Path>, format: OutputFormat) -> std::io::Result<()> {
        let file = &mut std::fs::File::create(path)?;
        self.emit(file, format)
    }

    fn fn_decl(&mut self, node: GlobalNodeId) -> llvm::DValueRef {
        if let Some(&v) = self.fn_decls.get(&node) {
            return v;
        }

        let ty = self.typing(node);

        let package = &self.packages[node.0];
        let name = if package.resolve_data.entry_point() == Some(node.1) {
            "__main"
        } else {
            package.discover_data.fn_name(node.1).value.as_str()
        };
        let fn_ = self.llvm.add_function(&name, ty);
        assert!(self.fn_decls.insert(node, fn_).is_none());
        assert!(self.fn_body_todos.insert(node));

        fn_
    }

    fn fn_body(&mut self, fn_decl: GlobalNodeId) {
        let package = &self.packages[fn_decl.0];
        let FnDecl { args, body, .. } = package.hir.fn_decl(fn_decl.1);
        if let Some(body) = *body {
            let fn_ = self.fn_decls[&fn_decl];
            self.llvm.append_new_bb(fn_, "header");

            let allocas = &mut HashMap::new();

            for (i, &arg) in args.iter().enumerate() {
                let name = &package.hir.fn_decl_arg(arg).priv_name.value;
                let val = self.alloca(fn_, (package.id, arg), name);
                let param = fn_.param(i as u32);
                self.headerb.store(param, val);
                assert!(allocas.insert(arg, val).is_none());
            }

            let body_bb = self.llvm.append_new_bb(fn_, "body");
            self.bodyb.position_at_end(body_bb);

            let ret = self.expr(body, &mut ExprCtx {
                package,
                fn_,
                allocas,
            });
            self.bodyb.ret(ret.to_direct(self.bodyb));

            if allocas.is_empty() {
                fn_.entry_bb().delete();
            } else {
                self.headerb.position_at_end(fn_.entry_bb());
                self.headerb.br(body_bb);
            }
        }
    }

    fn expr(&mut self, node: NodeId, ctx: &mut ExprCtx) -> Value {
        match ctx.package.hir.node_kind(node).value {
            NodeKind::Block => {
                let Block { exprs } = ctx.package.hir.block(node);
                let mut r = None;
                for &expr in exprs {
                    r = Some(self.expr(expr, ctx));
                }
                r.unwrap_or_else(|| self.unit_literal().into())
            }
            NodeKind::FieldAccess => {
                let receiver = ctx.package.hir.field_access(node).receiver;
                let receiver = self.expr(receiver, ctx).indirect();
                let idx = ctx.package.check_data.field_access(node).idx;
                self.bodyb.gep(receiver, &mut [self.llvm.int_type(32).const_int(0),
                    self.llvm.int_type(32).const_int(idx as u128)]).into()
            }
            NodeKind::FnCall => {
                let FnCall { callee, kind, args } = ctx.package.hir.fn_call(node);
                if *kind != FnCallKind::Free {
                    todo!();
                }
                let callee = self.expr(*callee, ctx).to_direct(self.bodyb);
                let args_ll = &mut Vec::new();
                for &FnCallArg { value, .. } in args {
                    let v = self.expr(value, ctx).to_direct(self.bodyb);
                    args_ll.push(v);
                }
                self.bodyb.call(callee, args_ll).into()
            }
            NodeKind::FnDecl => {
                self.fn_decl((ctx.package.id, node)).into()
            }
            NodeKind::Let => {
                let &Let { decl } = ctx.package.hir.let_(node);

                let &LetDecl { init, .. } = ctx.package.hir.let_decl(decl);

                if let Some(init) = init {
                    let p = self.expr(decl, ctx).indirect();
                    let v = self.expr(init, ctx).to_direct(self.bodyb);
                    self.bodyb.store(v, p);
                }

                self.bool_literal(true).into()
            }
            NodeKind::IfExpr => {
                let fn_ = ctx.fn_;
                let package = ctx.package;

                let &IfExpr { cond, if_true, if_false } = ctx.package.hir.if_expr(node);
                let cond = self.expr(cond, ctx).to_direct(self.bodyb);

                let if_true_bb = self.llvm.append_new_bb(fn_, "__if_true");
                let if_false_bb = self.llvm.append_new_bb(fn_, "__if_false");
                let succ_bb = self.llvm.append_new_bb(fn_, "__if_succ");

                self.bodyb.cond_br(cond, if_true_bb, if_false_bb);

                let ret_var = *ctx.allocas.entry(node)
                    .or_insert_with(|| {
                        self.alloca(fn_, (package.id, node), "__if")
                    });

                self.bodyb.position_at_end(if_true_bb);
                let v = self.expr(if_true, ctx).to_direct(self.bodyb);
                self.bodyb.store(v, ret_var);
                self.bodyb.br(succ_bb);

                self.bodyb.position_at_end(if_false_bb);
                if let Some(if_false) = if_false {
                    let v = self.expr(if_false, ctx).to_direct(self.bodyb);
                    self.bodyb.store(v, ret_var);
                }
                self.bodyb.br(succ_bb);

                self.bodyb.position_at_end(succ_bb);
                ret_var.into()
            }
            NodeKind::FnDeclArg => ctx.allocas[&node].into(),
            NodeKind::LetDecl => {
                let fn_ = ctx.fn_;
                let package = ctx.package;
                Value::Indirect(*ctx.allocas.entry(node)
                    .or_insert_with(|| {
                        let name = package.hir.let_decl(node).name.value.as_str();
                        self.alloca(fn_, (package.id, node), name)
                    }))
            }
            NodeKind::Literal => {
                let lit = ctx.package.hir.literal(node);
                match lit {
                    &Literal::Bool(v) => self.bool_literal(v),
                    &Literal::Char(v) => self.char_literal(v),
                    Literal::String(v) => self.string_literal(v),
                    &Literal::Int(IntLiteral { value, .. }) => {
                        let ty = self.typing((ctx.package.id, node));
                        ty.const_int(value)
                    },
                    &Literal::Float(FloatLiteral { value, .. }) => {
                        let ty = self.typing((ctx.package.id, node));
                        ty.const_real(value)
                    },
                    Literal::Unit => self.unit_literal(),
                }.into()
            }
            NodeKind::Op => {
                let op = ctx.package.hir.op(node);
                match op {
                    &Op::Binary(BinaryOp { kind, left, right }) => {
                        let leftv = self.expr(left, ctx);
                        let rightv = self.expr(right, ctx).to_direct(self.bodyb);
                        use BinaryOpKind::*;
                        if kind.value == Assign {
                            self.bodyb.store(rightv, leftv.indirect());
                            self.unit_literal()
                        } else {
                            let leftv = leftv.to_direct(self.bodyb);
                            match kind.value {
                                Add => {
                                    match self.unaliased_typing((ctx.package.id, left)).data().as_number().unwrap() {
                                        NumberType::Float => self.bodyb.fadd(leftv, rightv),
                                        NumberType::Int => self.bodyb.add(leftv, rightv),
                                    }
                                },
                                Assign => unreachable!(),
                                | Eq
                                | Gt
                                | GtEq
                                | Lt
                                | LtEq
                                | NotEq => {
                                    use PrimitiveType::*;
                                    let prim_ty = *self.unaliased_typing((ctx.package.id, left)).data().as_primitive().expect("todo");
                                    if prim_ty == Unit {
                                        self.bool_literal(true)
                                    } else {
                                        match prim_ty.as_number().unwrap() {
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
                                            NumberType::Int => {
                                                let sign = prim_ty.int_sign().unwrap();

                                                use IntPredicate::*;
                                                let pred = match kind.value {
                                                    Eq => LLVMIntEQ,
                                                    Gt => if sign == Sign::Signed { LLVMIntSGT } else { LLVMIntUGT },
                                                    GtEq => if sign == Sign::Signed { LLVMIntSGE } else { LLVMIntUGE },
                                                    Lt => if sign == Sign::Signed { LLVMIntSLT } else { LLVMIntULT },
                                                    LtEq => if sign == Sign::Signed { LLVMIntSLE } else { LLVMIntULE },
                                                    NotEq => LLVMIntNE,
                                                    _ => unreachable!(),
                                                };
                                                self.bodyb.icmp(leftv, rightv, pred)
                                            }
                                        }
                                    }
                                },
                                Sub => {
                                    match self.unaliased_typing((ctx.package.id, left)).data().as_number().unwrap() {
                                        NumberType::Float => self.bodyb.fsub(leftv, rightv),
                                        NumberType::Int => self.bodyb.sub(leftv, rightv),
                                    }
                                },
                                Mul => {
                                    match self.unaliased_typing((ctx.package.id, left)).data().as_number().unwrap() {
                                        NumberType::Float => self.bodyb.fmul(leftv, rightv),
                                        NumberType::Int => self.bodyb.mul(leftv, rightv),
                                    }
                                },
                                Div => {
                                    self.div_or_rem(ctx.fn_, (ctx.package.id, left), rightv,
                                        || self.bodyb.sdiv(leftv, rightv),
                                        || self.bodyb.udiv(leftv, rightv),
                                        || self.bodyb.fdiv(leftv, rightv))
                                },
                                Rem => {
                                    self.div_or_rem(ctx.fn_, (ctx.package.id, left), rightv,
                                        || self.bodyb.srem(leftv, rightv),
                                        || self.bodyb.urem(leftv, rightv),
                                        || self.bodyb.frem(leftv, rightv))
                                },

                                _ => todo!("{:?}", kind)
                            }
                        }
                    },
                    &Op::Unary(UnaryOp { kind, arg }) => {
                        let argv = self.expr(arg, ctx).to_direct(self.bodyb);
                        use UnaryOpKind::*;
                        match kind.value {
                            Neg => {
                                match self.unaliased_typing((ctx.package.id, arg)).data().as_number().unwrap() {
                                    NumberType::Float => self.bodyb.fneg(argv),
                                    NumberType::Int => self.bodyb.neg(argv),
                                }
                            }
                            _ => todo!("{:?}", kind)
                        }
                    },
                }.into()
            }
            NodeKind::Path => {
                let reso = ctx.package.check_data.target_of(node);
                if reso.0 == ctx.package.id {
                    self.expr(reso.1, ctx)
                } else {
                    let package = &self.packages[reso.0];
                    self.expr(reso.1, &mut ExprCtx {
                        package,
                        fn_: ctx.fn_,
                        allocas: ctx.allocas,
                    })
                }
            }
            NodeKind::Struct => {
                self.unit_literal().into()
            }
            NodeKind::StructValue => {
                let StructValue { name, fields, .. } = ctx.package.hir.struct_value(node);
                if name.is_some() {
                    let struct_var = self.alloca(ctx.fn_, (ctx.package.id, node), "struct_init"); // TODO use actual type name
                    for &StructValueField { value, .. } in fields {
                        let field_val = self.expr(value, ctx).to_direct(self.bodyb);
                        let idx = ctx.package.check_data.field_access(value).idx;
                        let field_ptr = self.bodyb.gep(struct_var, &mut [
                            self.llvm.int_type(32).const_int(0),
                            self.llvm.int_type(32).const_int(idx as u128)]);
                        self.bodyb.store(field_val, field_ptr);
                    }
                    struct_var.into()
                } else {
                    if !fields.is_empty() {
                        todo!();
                    }
                    self.unit_literal().into()
                }
            }
            _ => todo!("{:?}", ctx.package.hir.node_kind(node))
        }
    }

    fn div_or_rem(&self,
        fn_: DValueRef,
        left: GlobalNodeId,
        rightv: DValueRef,
        signed: impl FnOnce() -> DValueRef,
        unsigned: impl FnOnce() -> DValueRef,
        float: impl FnOnce() -> DValueRef,
    ) -> DValueRef {
        let prim_ty = self.unaliased_typing(left).data().as_primitive().unwrap();
        match prim_ty.as_number().unwrap() {
            NumberType::Float => float(),
            NumberType::Int => {
                let panic_bb = self.llvm.append_new_bb(fn_, "__panic");
                let succ_bb = self.llvm.append_new_bb(fn_, "__succ");
                let cond = self.bodyb.icmp(rightv, rightv.type_().const_int(0), IntPredicate::LLVMIntEQ);
                self.bodyb.cond_br(cond, panic_bb, succ_bb);

                self.bodyb.position_at_end(panic_bb);
                self.llvm.intrinsic::<intrinsic::Trap>().call(self.bodyb);
                self.bodyb.unreachable();

                self.bodyb.position_at_end(succ_bb);
                match prim_ty.int_sign().unwrap() {
                    Sign::Signed => signed(),
                    Sign::Unsigned => unsigned(),
                }
            },
        }
    }

    fn bool_literal(&mut self, v: bool) -> llvm::DValueRef {
        let v = if v { 1 } else { 0 };
        self.prim_type(PrimitiveType::Bool).const_int(v)
    }

    fn char_literal(&mut self, v: char) -> llvm::DValueRef {
        self.prim_type(PrimitiveType::Char).const_int(v as u128)
    }

    fn string_literal(&mut self, v: &str) -> llvm::DValueRef {
        let g = self.llvm.add_global_const(self.llvm.const_string(v));
        let ptr = self.llvm.const_pointer_cast(g, self.llvm.pointer_type(self.llvm.int_type(8)));
        let len = self.prim_type(PrimitiveType::USize).const_int(v.len() as u128);
        self.prim_type(PrimitiveType::String).const_struct(&mut [ptr, len])
    }

    fn unit_literal(&self) -> llvm::DValueRef {
        self.llvm.const_struct(&mut [])
    }

    fn unalias(&self, ty: TypeId) -> TypeId {
        if let &TypeData::Type(ty) = self.packages[ty.0].check_data.type_(ty.1).data() {
            self.unalias(ty)
        } else {
            ty
        }
    }

    fn unaliased_typing(&self, node: GlobalNodeId) -> &Type {
        let ty = self.packages[node.0].check_data.typing(node.1);
        let unaliased = self.unalias(ty);
        self.packages[unaliased.0].check_data.type_(unaliased.1)
    }

    fn typing(&mut self, node: GlobalNodeId) -> llvm::TypeRef {
        let ty = self.packages[node.0].check_data.typing(node.1);
        self.type_(ty)
    }

    fn type_(&mut self, ty: TypeId) -> llvm::TypeRef {
        if let Some(&v) = self.types.get(&ty) {
            return v;
        }
        let unaliased = self.unalias(ty);
        if let Some(&v) = self.types.get(&unaliased) {
            assert!(self.types.insert(ty, v).is_none());
            return v;
        }
        let package = &self.packages[unaliased.0];
        let ty_ll = match package.check_data.type_(unaliased.1).data() {
            TypeData::Fn(FnType { args, result, .. }) => {
                let args_ty = &mut Vec::with_capacity(args.len());
                for &arg in args {
                    args_ty.push(self.type_(arg));
                }
                let res_ty = self.type_(*result);
                TypeRef::function(res_ty, args_ty)
            }
            &TypeData::Primitive(prim) => {
                self.make_prim_type(prim)
            }
            TypeData::UnknownNumber(_) => unreachable!(),
            TypeData::Struct(check::StructType { fields }) => {
                let package = &self.packages[unaliased.0];
                let node = package.check_data.type_(unaliased.1).node().1;
                // FIXME node might be StructValue for anon struct.
                let name = package.hir.struct_(package.discover_data.parent_of(node)).name.value.as_str();
                let tys = &mut Vec::new();
                for &field_ty in fields {
                    tys.push(self.type_(field_ty));
                }
                self.llvm.named_struct_type(name, tys)
            }
            _ => todo!(),
        };

        assert!(self.types.insert(ty, ty_ll).is_none());
        if unaliased != ty {
            assert!(self.types.insert(unaliased, ty_ll).is_none());
        }

        ty_ll
    }

    fn make_prim_type(&self, ty: PrimitiveType) -> TypeRef {
        use PrimitiveType::*;
        match ty {
            Bool => self.llvm.int_type(1),
            F32 => self.llvm.float_type(),
            F64 => self.llvm.double_type(),
            I8 | U8 => self.llvm.int_type(8),
            I16 | U16 => self.llvm.int_type(16),
            I32 | U32 | Char => self.llvm.int_type(32),
            I64 | U64 => self.llvm.int_type(64),
            I128 | U128 => self.llvm.int_type(128),
            ISize | USize => self.llvm.int_type(self.llvm.pointer_size_bits()),
            Unit => self.llvm.struct_type(&mut []),
            String => {
                self.llvm.named_struct_type("String", &mut [
                    self.llvm.pointer_type(self.llvm.int_type(8)),
                    self.llvm.int_type(self.llvm.pointer_size_bits()),
                ])
            },
        }
    }

    fn prim_type(&mut self, ty: PrimitiveType) -> TypeRef {
        self.type_((PackageId::std(), self.packages[PackageId::std()].check_data.primitive(ty)))
    }

    fn alloca(&mut self, fn_: DValueRef, node: GlobalNodeId, name: &str) -> IValueRef {
        let ty = self.packages[node.0].check_data.typing(node.1);
        let ty = self.type_(ty);
        self.headerb.position_at_end(fn_.entry_bb());
        self.headerb.alloca(name, ty)
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