mod llvm;

use std::collections::{hash_map, HashMap, HashSet};

use crate::hir::*;
use crate::package::{Package, Packages, GlobalNodeId, PackageId};
use crate::semantic::check::{self, *};
use crate::syntax::*;

use llvm::*;

pub use llvm::OutputFormat;

struct ExprCtx<'a> {
    package: &'a Package,
    fn_: DValueRef,
    allocas: &'a mut NodeMap<IValueRef>,
}

#[derive(Clone, Copy)]
enum Value {
    Direct(DValueRef),
    Indirect(IValueRef),
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

impl From<DValueRef> for Value {
    fn from(v: DValueRef) -> Self {
        Self::Direct(v)
    }
}

impl From<IValueRef> for Value {
    fn from(v: IValueRef) -> Self {
        Self::Indirect(v)
    }
}

pub struct Codegen<'a> {
    llvm: Llvm,
    bodyb: BuilderRef,
    headerb: BuilderRef,
    packages: &'a Packages,
    fn_defs: HashMap<(GlobalNodeId, TypeRef), DValueRef>,
    fn_body_todos: HashSet<(GlobalNodeId, TypeRef)>,
    types: TypeMap<TypeRef>,
    defined_types: HashMap<(GlobalNodeId, TypeRef), TypeRef>,
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
            fn_defs: HashMap::new(),
            fn_body_todos: HashSet::new(),
            types: HashMap::new(),
            defined_types: HashMap::new(),
        }
    }

    pub fn lower(&mut self, package_id: PackageId) {
        let entry_point = self.packages[package_id].check_data.entry_point().unwrap();

        self.fn_def((package_id, entry_point));

        while let Some(&(node, ty_args)) = self.fn_body_todos.iter().next() {
            self.fn_body(node, ty_args);
            assert!(self.fn_body_todos.remove(&(node, ty_args)));
        }
    }

    pub fn emit(&self, out: &mut impl std::io::Write, format: OutputFormat) -> std::io::Result<()> {
        self.llvm.emit(out, format)
    }

    pub fn emit_to_file(&self, path: impl AsRef<std::path::Path>, format: OutputFormat) -> std::io::Result<()> {
        let file = &mut std::fs::File::create(path)?;
        self.emit(file, format)
    }

    fn fn_def(&mut self, node: GlobalNodeId) -> DValueRef {
        let ty = self.packages.typing(node);
        let ty = self.packages.type_(ty);
        let ty_args = self.unit_literal().type_();
        if let Some(&v) = self.fn_defs.get(&(node, ty_args)) {
            return v;
        }

        let package = &self.packages[node.0];
        let name = if package.check_data.entry_point() == Some(node.1) {
            "__main"
        } else {
            package.hir.fn_def(node.1).name.value.as_str()
        };
        let ty_ll = self.type_(ty.id);
        let fn_ = self.llvm.add_function(&name, ty_ll);
        assert!(self.fn_defs.insert((node, ty_args), fn_).is_none());
        assert!(self.fn_body_todos.insert((node, ty_args)));

        fn_
    }

    fn fn_body(&mut self, fn_def: GlobalNodeId, ty_args: TypeRef) {
        let package = &self.packages[fn_def.0];
        let FnDef { params, body, .. } = package.hir.fn_def(fn_def.1);
        if let Some(body) = *body {
            let fn_ = self.fn_defs[&(fn_def, ty_args)];
            self.llvm.append_new_bb(fn_, "header");

            let allocas = &mut HashMap::new();
            let ctx = &mut ExprCtx {
                package,
                fn_,
                allocas,
            };

            for (i, &param) in params.iter().enumerate() {
                let name = &package.hir.fn_def_param(param).name.value;
                let val = self.alloca(param, name, ctx);
                let param = fn_.param(i as u32);
                self.headerb.store(param, val);
            }

            let body_bb = self.llvm.append_new_bb(fn_, "body");
            self.bodyb.position_at_end(body_bb);

            let ret = self.expr(body, ctx);
            let ret = ret.to_direct(self.bodyb);
            self.bodyb.ret(ret);

            if allocas.is_empty() {
                fn_.entry_bb().delete();
            } else {
                self.headerb.position_at_end(fn_.entry_bb());
                self.headerb.br(body_bb);
            }
        }
    }

    fn ensure_indirect(&mut self, node: NodeId, v: Value, ctx: &mut ExprCtx) -> IValueRef {
        match v {
            Value::Direct(v) => {
                let tmp = self.alloca_ty(node, v.type_(), "", ctx);
                self.bodyb.store(v, tmp);
                tmp
            }
            Value::Indirect(v) => v,
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
                let receiver = self.expr(receiver, ctx);
                let receiver = self.ensure_indirect(node, receiver, ctx);
                let idx = ctx.package.check_data.struct_field_index(node);
                self.bodyb.struct_gep(receiver, idx).into()
            }
            NodeKind::FnCall => {
                let fnc = ctx.package.hir.fn_call(node);

                let ty_args = fnc.callee_path_item(&ctx.package.hir).1.ty_args.as_ref()
                    .map(|v| v.value.len()).unwrap_or(0);
                if ty_args != 0 {
                    todo!();
                }

                let callee = self.expr(fnc.callee, ctx).to_direct(self.bodyb);
                let args_ll = &mut Vec::new();
                for &FnCallArg { value, .. } in &fnc.args {
                    let v = self.expr(value, ctx).to_direct(self.bodyb);
                    args_ll.push(v);
                }
                self.bodyb.call(callee, args_ll).into()
            }
            NodeKind::Let => {
                let &Let { def } = ctx.package.hir.let_(node);

                let &LetDef { init, .. } = ctx.package.hir.let_def(def);

                if let Some(init) = init {
                    let p = self.expr(def, ctx).indirect();
                    let v = self.expr(init, ctx).to_direct(self.bodyb);
                    self.bodyb.store(v, p);
                }

                self.bool_literal(true).into()
            }
            NodeKind::IfExpr => {
                let fn_ = ctx.fn_;

                let &IfExpr { cond, if_true, if_false } = ctx.package.hir.if_expr(node);
                let cond = self.expr(cond, ctx).to_direct(self.bodyb);

                let if_true_bb = self.llvm.append_new_bb(fn_, "__if_true");
                let if_false_bb = self.llvm.append_new_bb(fn_, "__if_false");
                let succ_bb = self.llvm.append_new_bb(fn_, "__if_succ");

                self.bodyb.cond_br(cond, if_true_bb, if_false_bb);

                let ret_var = self.alloca(node, "__if", ctx);

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
            NodeKind::FnDefParam => ctx.allocas[&node].into(),
            NodeKind::LetDef => {
                let name = ctx.package.hir.let_def(node).name.value.as_str();
                Value::Indirect(self.alloca(node, name, ctx))
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
                        let left_ty = self.typing_hl((ctx.package.id, left));
                        use BinaryOpKind::*;
                        if kind.value == Assign {
                            self.bodyb.store(rightv, leftv.indirect());
                            self.unit_literal()
                        } else {
                            let leftv = leftv.to_direct(self.bodyb);
                            match kind.value {
                                Add => {
                                    match self.packages.as_number_type(left_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fadd(leftv, rightv),
                                        NumberType::Int { signed: _ } => self.bodyb.add(leftv, rightv),
                                    }
                                },
                                Assign => unreachable!(),
                                | Eq
                                | Gt
                                | GtEq
                                | Lt
                                | LtEq
                                | NotEq => {
                                    if self.packages.is_unit_type(left_ty) {
                                        self.bool_literal(true)
                                    } else {
                                        match self.packages.as_number_type(left_ty).expect("todo") {
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
                                        }
                                    }
                                },
                                Sub => {
                                    match self.packages.as_number_type(left_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fsub(leftv, rightv),
                                        NumberType::Int { signed: _ } => self.bodyb.sub(leftv, rightv),
                                    }
                                },
                                Mul => {
                                    match self.packages.as_number_type(left_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fmul(leftv, rightv),
                                        NumberType::Int { signed: _ } => self.bodyb.mul(leftv, rightv),
                                    }
                                },
                                Div => {
                                    self.div_or_rem(ctx.fn_, left_ty, rightv,
                                        || self.bodyb.sdiv(leftv, rightv),
                                        || self.bodyb.udiv(leftv, rightv),
                                        || self.bodyb.fdiv(leftv, rightv))
                                },
                                Rem => {
                                    self.div_or_rem(ctx.fn_, left_ty, rightv,
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
                        let arg_ty = self.typing_hl((ctx.package.id, arg));
                        use UnaryOpKind::*;
                        match kind.value {
                            Neg => {
                                match self.packages.as_number_type(arg_ty).expect("todo") {
                                    NumberType::Float => self.bodyb.fneg(argv),
                                    NumberType::Int { signed: _ } => self.bodyb.neg(argv),
                                }
                            }
                            _ => todo!("{:?}", kind)
                        }
                    },
                }.into()
            }
            NodeKind::Path => {
                let reso = ctx.package.check_data.target_of(node);
                let package = &self.packages[reso.0];
                if package.hir.node_kind(reso.1).value == NodeKind::FnDef {
                    self.fn_def(reso).into()
                } else {
                    self.expr(reso.1, &mut ExprCtx {
                        package,
                        fn_: ctx.fn_,
                        allocas: ctx.allocas,
                    })
                }
            }
            NodeKind::StructValue => {
                let StructValue { fields, .. } = ctx.package.hir.struct_value(node);
                if fields.is_empty() {
                    let ty = ctx.package.check_data.typing(node);
                    let ty = self.type_(ty);
                    ty.const_struct(&mut []).into()
                } else {
                    let struct_var = self.alloca(node, "struct_init", ctx); // TODO use actual type name
                    for &field in fields {
                        let value = ctx.package.hir.struct_value_field(field).value;
                        let field_val = self.expr(value, ctx).to_direct(self.bodyb);
                        let idx = ctx.package.check_data.struct_field_index(field);
                        let field_ptr = self.bodyb.struct_gep(struct_var, idx);
                        self.bodyb.store(field_val, field_ptr);
                    }
                    struct_var.into()
                }
            }
            NodeKind::StructValueField => unreachable!(),
            NodeKind::While => {
                let &While { cond, block } = ctx.package.hir.while_(node);

                let cond_bb = self.llvm.append_new_bb(ctx.fn_, "__while_cond");
                let block_bb = self.llvm.append_new_bb(ctx.fn_, "__while_block");
                let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__while_succ");

                self.bodyb.br(cond_bb);

                self.bodyb.position_at_end(cond_bb);
                let cond = self.expr(cond, ctx).to_direct(self.bodyb);
                self.bodyb.cond_br(cond, block_bb, succ_bb);

                self.bodyb.position_at_end(block_bb);
                self.expr(block, ctx);
                self.bodyb.br(cond_bb);

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
        }
    }

    fn div_or_rem(&self,
        fn_: DValueRef,
        left_ty: TypeId,
        rightv: DValueRef,
        make_signed: impl FnOnce() -> DValueRef,
        make_unsigned: impl FnOnce() -> DValueRef,
        make_float: impl FnOnce() -> DValueRef,
    ) -> DValueRef {
        match self.packages.as_number_type(left_ty).expect("todo") {
            NumberType::Float => make_float(),
            NumberType::Int { signed } => {
                let panic_bb = self.llvm.append_new_bb(fn_, "__panic");
                let succ_bb = self.llvm.append_new_bb(fn_, "__succ");
                let cond = self.bodyb.icmp(rightv, rightv.type_().const_int(0), IntPredicate::LLVMIntEQ);
                self.bodyb.cond_br(cond, panic_bb, succ_bb);

                self.bodyb.position_at_end(panic_bb);
                self.llvm.intrinsic::<intrinsic::Trap>().call(self.bodyb);
                self.bodyb.unreachable();

                self.bodyb.position_at_end(succ_bb);
                if signed {
                    make_signed()
                } else {
                    make_unsigned()
                }
            },
        }
    }

    fn bool_literal(&mut self, v: bool) -> DValueRef {
        let v = if v { 1 } else { 0 };
        self.lang_type(LangItem::Primitive(PrimitiveType::Bool)).const_int(v)
    }

    fn char_literal(&mut self, v: char) -> DValueRef {
        self.lang_type(LangItem::Primitive(PrimitiveType::Char)).const_int(v as u128)
    }

    fn string_literal(&mut self, v: &str) -> DValueRef {
        let g = self.llvm.add_global_const(self.llvm.const_string(v));
        let ptr = self.llvm.const_pointer_cast(g, self.llvm.pointer_type(self.llvm.int_type(8)));
        let len = self.lang_type(LangItem::Primitive(PrimitiveType::USize)).const_int(v.len() as u128);
        let ty = self.lang_type(LangItem::String);
        ty.const_struct(&mut [ptr, len])
    }

    fn unit_literal(&mut self) -> DValueRef {
        self.type_(self.packages.std().check_data.lang().unit_type())
            .const_struct(&mut [])
    }

    fn typing_hl(&self, node: GlobalNodeId) -> TypeId {
        self.packages[node.0].check_data.typing(node.1)
    }

    fn typing(&mut self, node: GlobalNodeId) -> TypeRef {
        let ty = self.packages[node.0].check_data.typing(node.1);
        self.type_(ty)
    }

    fn type_(&mut self, ty: TypeId) -> TypeRef {
        dbg!(ty);
        let ty = self.packages[ty.0].check_data.try_normalized_type(ty)
            .unwrap_or_else(|| {
                let ty = self.packages.type_term(ty);
                assert!(ty.data.as_fn().is_some());
                ty.id
            });
        if let Some(&v) = self.types.get(&ty) {
            return v;
        }
        let ty = self.packages.type_(ty);

        let ty_ll = match &ty.data {
            TypeData::Fn(FnType { params, result, unsafe_: _, }) => {
                let param_tys = &mut Vec::with_capacity(params.len());
                for &param in params {
                    param_tys.push(self.type_(param));
                }
                let res_ty = self.type_(*result);
                TypeRef::function(res_ty, param_tys)
            }
            TypeData::Struct(v) => self.make_struct_type(v),
            TypeData::Var(_) => todo!(),
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            => unreachable!("{:?}", ty),
        };
        assert!(self.types.insert(ty.id, ty_ll).is_none());
        ty_ll
    }

    fn make_struct_type(&mut self, sty: &check::StructType) -> TypeRef {
        let check::StructType { def, fields } = sty;
        if let Some(def) = *def {
            if let Some(prim) = self.packages.std().check_data.lang().as_primitive(def) {
                return self.make_prim_type(prim);
            } else if let Some(LangItem::String) = self.packages.std().check_data.lang().as_item(def) {
                // FIXME this won't be needed once there's a reference type in frontend.
                let fields = &mut vec![
                    self.llvm.pointer_type(self.llvm.int_type(8)),
                    self.llvm.int_type(self.llvm.pointer_size_bits()),
                ];
                return self.make_struct_type0(Some(def), fields);
            }
        }
        let field_tys = &mut Vec::with_capacity(fields.len());
        for &check::StructTypeField { name: _, ty } in fields {
            field_tys.push(self.type_(ty));
        }
        self.make_struct_type0(*def, field_tys)
    }

    fn make_struct_type0(&mut self, def: Option<GlobalNodeId>, fields: &mut [TypeRef]) -> TypeRef {
        let shape = self.llvm.struct_type(fields);
        if let Some(def) = def {
            match self.defined_types.entry((def, shape)) {
                hash_map::Entry::Occupied(e) => {
                    *e.get()
                }
                hash_map::Entry::Vacant(e) => {
                    let name = &self.packages[def.0].hir.struct_(def.1).name.value;
                    let ty = self.llvm.named_struct_type(name, fields);
                    e.insert(ty);
                    ty
                }
            }
        } else {
            shape
        }
    }

    fn make_prim_type(&self, prim_ty: PrimitiveType) -> TypeRef {
        use PrimitiveType::*;
        match prim_ty {
            Bool => self.llvm.int_type(1),
            F32 => self.llvm.float_type(),
            F64 => self.llvm.double_type(),
            I8 | U8 => self.llvm.int_type(8),
            I16 | U16 => self.llvm.int_type(16),
            I32 | U32 | Char => self.llvm.int_type(32),
            I64 | U64 => self.llvm.int_type(64),
            I128 | U128 => self.llvm.int_type(128),
            ISize | USize => self.llvm.int_type(self.llvm.pointer_size_bits()),
        }
    }

    fn lang_type(&mut self, lang_item: LangItem) -> TypeRef {
        self.type_(self.packages.std().check_data.lang().type_(lang_item))
    }

    fn alloca(&mut self, node: NodeId, name: &str, ctx: &mut ExprCtx) -> IValueRef {
        let ty = ctx.package.check_data.typing(node);
        let ty = self.type_(ty);
        self.alloca_ty(node, ty, name, ctx)
    }

    fn alloca_ty(&mut self, node: NodeId, ty: TypeRef, name: &str, ctx: &mut ExprCtx) -> IValueRef {
        let fn_ = ctx.fn_;
        *ctx.allocas.entry(node)
            .or_insert_with(|| {
                self.headerb.position_at_end(fn_.entry_bb());
                let val = self.headerb.alloca(name, ty);
                val
            })
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