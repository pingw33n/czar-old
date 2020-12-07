mod llvm;

use std::collections::{hash_map, HashMap};

use crate::hir::*;
use crate::package::{Package, Packages, GlobalNodeId, PackageId};
use crate::semantic::check::{self, *};
use crate::syntax::*;

use llvm::*;

pub use llvm::OutputFormat;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct GenericEnvId(TypeRef);

struct GenericEnv {
    id: GenericEnvId,
    vars: TypeVarMap,
}

struct ExprCtx<'a> {
    package: &'a Package,
    fn_: ValueRef,
    allocas: &'a mut NodeMap<Value>,
    alloca_count: usize,
    genv: &'a GenericEnv,
}

#[derive(Clone, Copy)]
enum Value {
    Direct(ValueRef),
    Indirect(ValueRef),
}

impl Value {
    fn ptr(self) -> ValueRef {
        match self {
            Self::Direct(v) => panic!("expected indirect value but found: {:?}", v),
            Self::Indirect(v) => v,
        }
    }

    fn deref(self, b: llvm::BuilderRef) -> ValueRef {
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

type TopLevelMonoId = (GlobalNodeId, GenericEnvId);
type MonoId = (TypeId, GenericEnvId);

#[derive(Clone, Copy)]
struct FnDecl {
    ll: ValueRef,
}

struct FnMonoRequest {
    genv_vars: TypeVarMap,
}

pub struct Codegen<'a> {
    llvm: Llvm,
    bodyb: BuilderRef,
    headerb: BuilderRef,
    packages: &'a Packages,
    fn_decls: HashMap<TopLevelMonoId, FnDecl>,
    fn_mono_reqs: HashMap<TopLevelMonoId, FnMonoRequest>,
    types: HashMap<MonoId, TypeRef>,
    defined_types: HashMap<TopLevelMonoId, TypeRef>,
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
            fn_mono_reqs: HashMap::new(),
            types: HashMap::new(),
            defined_types: HashMap::new(),
        }
    }

    pub fn lower(&mut self, package_id: PackageId) {
        let entry_point = self.packages[package_id].check_data.entry_point().unwrap();
        let node = self.packages.underlying_type(entry_point).data.name().unwrap();

        self.fn_def(node, entry_point, &self.default_genv());

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

    fn default_genv(&self) -> GenericEnv {
        GenericEnv {
            id: GenericEnvId(self.llvm.struct_type(&mut [])),
            vars: TypeVarMap::default(),
        }
    }

    fn normalized(&self, ty: TypeId) -> TypeId {
        self.packages[ty.0].check_data.normalized_type(ty)
    }

    fn make_genv_id(&mut self, ty_vars: &TypeVarMap, genv: &GenericEnv) -> GenericEnvId {
        let mut ty_vars: Vec<_> = ty_vars.iter().collect();
        ty_vars.sort_by_key(|&(k, _)| k);
        let mut genv_id = Vec::with_capacity(ty_vars.len());
        for (_, ty) in ty_vars {
            genv_id.push(self.type_(ty, genv));
        }
        GenericEnvId(self.make_struct_type0(None, &mut genv_id))
    }

    fn fn_def(&mut self, fn_def: GlobalNodeId, ty: TypeId, genv: &GenericEnv) -> Value {
        let ty = self.normalized(ty);
        let mut genv_vars = self.packages.type_(ty).data.as_generic_env().map(|v| v.vars.clone()).unwrap_or_default();
        genv_vars.replace_iter(genv.vars.iter());
        let genv_id = self.make_genv_id(&genv_vars, genv);

        let mid = (fn_def, genv_id);
        if let Some(&v) = self.fn_decls.get(&mid) {
            return v.ll.direct();
        }

        let package = &self.packages[fn_def.0];
        let name = if package.check_data.entry_point() == Some(ty) {
            "__main"
        } else {
            package.hir.fn_def(fn_def.1).name.value.as_str()
        };
        let ty = self.packages.type_(ty);
        let ty_ll = self.type_(ty.id, genv);
        let fn_ = self.llvm.add_function(&name, ty_ll);
        assert!(self.fn_decls.insert(mid, FnDecl {
            ll: fn_,
        }).is_none());
        assert!(self.fn_mono_reqs.insert(mid, FnMonoRequest {
            genv_vars,
        }).is_none());

        fn_.direct()
    }

    fn mono_fn(&mut self, id: TopLevelMonoId, req: FnMonoRequest) {
        let fn_def = id.0;
        let package = &self.packages[fn_def.0];
        let FnDef { params, body, .. } = package.hir.fn_def(fn_def.1);
        if let Some(body) = *body {
            let FnDecl { ll: fn_ } = self.fn_decls[&id];
            self.llvm.append_new_bb(fn_, "entry");

            let allocas = &mut HashMap::new();
            let ctx = &mut ExprCtx {
                package,
                fn_,
                allocas,
                alloca_count: 0,
                genv: &GenericEnv {
                    id: id.1,
                    vars: req.genv_vars,
                },
            };

            for (i, &param) in params.iter().enumerate() {
                let name = &package.hir.fn_def_param(param).name.value;
                let val = self.alloca(param, name, ctx);
                let param = fn_.param(i as u32);
                self.headerb.store(param, val.ptr());
            }

            let body_bb = self.llvm.append_new_bb(fn_, "body");
            self.bodyb.position_at_end(body_bb);

            let ret = self.expr(body, ctx);
            let ret = ret.deref(self.bodyb);
            self.bodyb.ret(ret);

            if ctx.alloca_count == 0 {
                fn_.entry_bb().delete();
            } else {
                self.headerb.position_at_end(fn_.entry_bb());
                self.headerb.br(body_bb);
            }
        }
    }

    fn make_ptr(&mut self, v: Value, ctx: &mut ExprCtx) -> ValueRef {
        match v {
            Value::Direct(v) => {
                let tmp = self.alloca_new(v.type_(), "", ctx).ptr();
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
                let receiver = self.make_ptr(receiver, ctx);
                let idx = ctx.package.check_data.struct_field_index(node);
                self.bodyb.struct_gep(receiver, idx).indirect()
            }
            NodeKind::FnCall => {
                let fnc = ctx.package.hir.fn_call(node);

                let callee = self.expr(fnc.callee, ctx).deref(self.bodyb);
                let args_ll = &mut Vec::new();
                for &FnCallArg { value, .. } in &fnc.args {
                    let v = self.expr(value, ctx).deref(self.bodyb);
                    args_ll.push(v);
                }
                self.bodyb.call(callee, args_ll).direct()
            }
            NodeKind::Let => {
                let &Let { def } = ctx.package.hir.let_(node);

                let &LetDef { init, .. } = ctx.package.hir.let_def(def);

                if let Some(init) = init {
                    let p = self.expr(def, ctx).ptr();
                    let v = self.expr(init, ctx).deref(self.bodyb);
                    self.bodyb.store(v, p);
                }

                self.bool_literal(true)
            }
            NodeKind::IfExpr => {
                let fn_ = ctx.fn_;

                let &IfExpr { cond, if_true, if_false } = ctx.package.hir.if_expr(node);
                let cond = self.expr(cond, ctx).deref(self.bodyb);

                let if_true_bb = self.llvm.append_new_bb(fn_, "__if_true");
                let if_false_bb = self.llvm.append_new_bb(fn_, "__if_false");
                let succ_bb = self.llvm.append_new_bb(fn_, "__if_succ");

                self.bodyb.cond_br(cond, if_true_bb, if_false_bb);

                let ret_var = self.alloca(node, "__if", ctx).ptr();

                self.bodyb.position_at_end(if_true_bb);
                let v = self.expr(if_true, ctx).deref(self.bodyb);
                self.bodyb.store(v, ret_var);
                self.bodyb.br(succ_bb);

                self.bodyb.position_at_end(if_false_bb);
                if let Some(if_false) = if_false {
                    let v = self.expr(if_false, ctx).deref(self.bodyb);
                    self.bodyb.store(v, ret_var);
                }
                self.bodyb.br(succ_bb);

                self.bodyb.position_at_end(succ_bb);
                ret_var.indirect()
            }
            NodeKind::FnDefParam => ctx.allocas[&node].into(),
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
                        let ty = self.typing((ctx.package.id, node), ctx.genv);
                        ty.const_int(value).direct()
                    },
                    &Literal::Float(FloatLiteral { value, .. }) => {
                        let ty = self.typing((ctx.package.id, node), ctx.genv);
                        ty.const_real(value).direct()
                    },
                    Literal::Unit => self.unit_literal(),
                }.into()
            }
            NodeKind::Op => {
                let op = ctx.package.hir.op(node);
                match op {
                    &Op::Binary(BinaryOp { kind, left, right }) => {
                        let leftv = self.expr(left, ctx);
                        let rightv = self.expr(right, ctx).deref(self.bodyb);
                        let left_ty = self.packages.typing((ctx.package.id, left));
                        use BinaryOpKind::*;
                        if kind.value == Assign {
                            self.bodyb.store(rightv, leftv.ptr());
                            self.unit_literal()
                        } else {
                            let leftv = leftv.deref(self.bodyb);
                            match kind.value {
                                Add => {
                                    match self.packages.as_number_type(left_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fadd(leftv, rightv),
                                        NumberType::Int { signed: _ } => self.bodyb.add(leftv, rightv),
                                    }.direct()
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
                                        }.direct()
                                    }
                                },
                                Sub => {
                                    match self.packages.as_number_type(left_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fsub(leftv, rightv),
                                        NumberType::Int { signed: _ } => self.bodyb.sub(leftv, rightv),
                                    }.direct()
                                },
                                Mul => {
                                    match self.packages.as_number_type(left_ty).expect("todo") {
                                        NumberType::Float => self.bodyb.fmul(leftv, rightv),
                                        NumberType::Int { signed: _ } => self.bodyb.mul(leftv, rightv),
                                    }.direct()
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
                        let argv = self.expr(arg, ctx).deref(self.bodyb);
                        let arg_ty = self.packages.typing((ctx.package.id, arg));
                        use UnaryOpKind::*;
                        match kind.value {
                            Neg => {
                                match self.packages.as_number_type(arg_ty).expect("todo") {
                                    NumberType::Float => self.bodyb.fneg(argv),
                                    NumberType::Int { signed: _ } => self.bodyb.neg(argv),
                                }
                            }
                            _ => todo!("{:?}", kind)
                        }.direct()
                    },
                }
            }
            NodeKind::Path => {
                let reso = ctx.package.check_data.target_of(node);
                let package = &self.packages[reso.0];
                if package.hir.node_kind(reso.1).value == NodeKind::FnDef {
                    self.fn_def(reso, ctx.package.check_data.typing(node), ctx.genv)
                } else {
                    self.expr(reso.1, &mut ExprCtx {
                        package,
                        fn_: ctx.fn_,
                        allocas: ctx.allocas,
                        alloca_count: ctx.alloca_count,
                        genv: ctx.genv,
                    })
                }
            }
            NodeKind::Range => {
                let &Range { kind: _, start, end } = ctx.package.hir.range(node);

                let struct_var = self.alloca(node, "range_literal", ctx);

                let mut idx = 0;
                for &v in &[start, end] {
                    if let Some(v) = v {
                        let v = self.expr(v, ctx).deref(self.bodyb);
                        let ptr = self.bodyb.struct_gep(struct_var.ptr(), idx);
                        self.bodyb.store(v, ptr);
                        idx += 1;
                    }
                }

                struct_var
            }
            NodeKind::StructLiteral => {
                let StructLiteral { fields, .. } = ctx.package.hir.struct_literal(node);
                if fields.is_empty() {
                    let ty = ctx.package.check_data.typing(node);
                    let ty = self.type_(ty, ctx.genv);
                    ty.const_struct(&mut []).direct()
                } else {
                    let struct_var = self.alloca(node, "struct_init", ctx); // TODO use actual type name
                    for &field in fields {
                        let value = ctx.package.hir.struct_literal_field(field).value;
                        let field_val = self.expr(value, ctx).deref(self.bodyb);
                        let idx = ctx.package.check_data.struct_field_index(field);
                        let field_ptr = self.bodyb.struct_gep(struct_var.ptr(), idx);
                        self.bodyb.store(field_val, field_ptr);
                    }
                    struct_var.into()
                }
            }
            NodeKind::StructLiteralField => unreachable!(),
            NodeKind::While => {
                let &While { cond, block } = ctx.package.hir.while_(node);

                let cond_bb = self.llvm.append_new_bb(ctx.fn_, "__while_cond");
                let block_bb = self.llvm.append_new_bb(ctx.fn_, "__while_block");
                let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__while_succ");

                self.bodyb.br(cond_bb);

                self.bodyb.position_at_end(cond_bb);
                let cond = self.expr(cond, ctx).deref(self.bodyb);
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
        fn_: ValueRef,
        left_ty: TypeId,
        rightv: ValueRef,
        make_signed: impl FnOnce() -> ValueRef,
        make_unsigned: impl FnOnce() -> ValueRef,
        make_float: impl FnOnce() -> ValueRef,
    ) -> Value {
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
        }.direct()
    }

    fn bool_literal(&mut self, v: bool) -> Value {
        let v = if v { 1 } else { 0 };
        self.lang_type(LangItem::Primitive(PrimitiveType::Bool)).const_int(v).direct()
    }

    fn char_literal(&mut self, v: char) -> Value {
        self.lang_type(LangItem::Primitive(PrimitiveType::Char)).const_int(v as u128).direct()
    }

    fn string_literal(&mut self, v: &str) -> Value {
        let g = self.llvm.add_global_const(self.llvm.const_string(v));
        let ptr = self.llvm.const_pointer_cast(g, self.llvm.pointer_type(self.llvm.int_type(8)));
        let len = self.lang_type(LangItem::Primitive(PrimitiveType::USize)).const_int(v.len() as u128);
        let ty = self.lang_type(LangItem::String);
        ty.const_struct(&mut [ptr, len]).direct()
    }

    fn unit_literal(&mut self) -> Value {
        self.type_(self.packages.std().check_data.lang().unit_type(), &self.default_genv())
            .const_struct(&mut [])
            .direct()
    }

    fn typing(&mut self, node: GlobalNodeId, genv: &GenericEnv) -> TypeRef {
        let ty = self.packages[node.0].check_data.typing(node.1);
        self.type_(ty, genv)
    }

    fn type_(&mut self, ty: TypeId, genv: &GenericEnv) -> TypeRef {
        let ty = self.normalized(ty);
        if let Some(&v) = self.types.get(&(ty, genv.id)) {
            return v;
        }
        let uty = self.packages.underlying_type(ty);
        let ty_ll = match &uty.data {
            TypeData::Fn(FnType { name: _, params, result, unsafe_: _, }) => {
                let param_tys = &mut Vec::with_capacity(params.len());
                for &param in params {
                    param_tys.push(self.type_(param, genv));
                }
                let res_ty = self.type_(*result, genv);
                TypeRef::function(res_ty, param_tys)
            }
            TypeData::GenericEnv(check::GenericEnv { ty, vars: _ }) => self.type_(*ty, genv),
            TypeData::Struct(v) => self.make_struct_type(ty, v, genv),
            TypeData::Var(_) => {
                let ty = genv.vars.get(uty.id).unwrap();
                self.type_(ty, genv)
            },
            | TypeData::Ctor(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            => unreachable!("{:?}", uty),
        };
        assert!(self.types.insert((ty, genv.id), ty_ll).is_none());
        ty_ll
    }

    fn make_struct_type(&mut self, ty: TypeId, sty: &check::StructType, genv: &GenericEnv) -> TypeRef {
        let check::StructType { name: def, fields } = sty;
        if let Some(def) = *def {
            if let Some(prim) = self.packages.std().check_data.lang().as_primitive(def) {
                return self.make_prim_type(prim);
            } else if let Some(LangItem::Ptr) = self.packages.std().check_data.lang().as_item(def) {
                let pty = self.packages.type_(ty).data.as_generic_env().unwrap().vars.vals().next().unwrap();
                let pty = self.type_(pty, genv);
                return self.llvm.pointer_type(pty)
            }
        }
        let field_tys = &mut Vec::with_capacity(fields.len());
        for &check::StructTypeField { name: _, ty } in fields {
            field_tys.push(self.type_(ty, genv));
        }
        self.make_struct_type0(*def, field_tys)
    }

    fn make_struct_type0(&mut self, def: Option<GlobalNodeId>, fields: &mut [TypeRef]) -> TypeRef {
        let shape = self.llvm.struct_type(fields);
        if let Some(def) = def {
            match self.defined_types.entry((def, GenericEnvId(shape))) {
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
        self.type_(self.packages.std().check_data.lang().type_(lang_item), &self.default_genv())
    }

    fn alloca(&mut self, node: NodeId, name: &str, ctx: &mut ExprCtx) -> Value {
        let ty = ctx.package.check_data.typing(node);
        let ty = self.type_(ty, ctx.genv);
        if ctx.allocas.contains_key(&node) {
            ctx.allocas[&node]
        } else {
            let r = self.alloca_new(ty, name, ctx);
            assert!(ctx.allocas.insert(node, r).is_none());
            r
        }
    }

    fn alloca_new(&mut self, ty: TypeRef, name: &str, ctx: &mut ExprCtx) -> Value {
        ctx.alloca_count += 1;
        self.headerb.position_at_end(ctx.fn_.entry_bb());
        self.headerb.alloca(name, ty).indirect()
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