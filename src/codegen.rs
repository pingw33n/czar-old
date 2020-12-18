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

#[derive(Clone, Copy, Debug)]
enum Value {
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

    fn find_type_param_deps(&self, ty: TypeId) -> Vec<TypeId> {
        let mut r = Vec::new();
        self.find_type_param_deps0(ty, &mut r);
        r
    }

    fn find_type_param_deps0(&self, ty: TypeId, r: &mut Vec<TypeId>) {
        match &self.packages.type_(ty).data {
            TypeData::GenericEnv(_) => {}
            TypeData::Fn(FnType { name, params, result, unsafe_: _ }) => {
                assert!(name.is_none());
                for &param in params {
                    self.find_type_param_deps0(param, r);
                }
                self.find_type_param_deps0(*result, r);
            }
            &TypeData::Slice(check::SliceType { item, len: _ }) => {
                self.find_type_param_deps0(item, r);
            }
            TypeData::Struct(check::StructType { name, fields }) => {
                assert!(name.is_none());
                for &check::StructTypeField { name: _, ty } in fields {
                    self.find_type_param_deps0(ty, r);
                }
            }
            TypeData::Var(Var::Param(_)) => r.push(ty),

            | TypeData::Ctor(_)
            | TypeData::Incomplete(_)
            | TypeData::Instance(_)
            | TypeData::Var(Var::Inference(_))
            => unreachable!(),
        }
    }

    fn resolve_fn_genv_vars(&self, ty: TypeId, outer: &GenericEnv) -> TypeVarMap {
        let mut r = self.packages.type_(ty).data.as_generic_env().map(|v| v.vars.clone()).unwrap_or_default();
        let mut more = Vec::new();
        for (_, val) in r.iter_mut() {
            if let Some(v) = outer.vars.get(*val) {
                *val = v;
            }
            more.extend_from_slice(&self.find_type_param_deps(*val));
        }
        for var in more {
            if r.get(var).is_none() {
                if let Some(val) = outer.vars.get(var) {
                    r.insert(var, val);
                }
            }
        }

        r
    }

    fn fn_def(&mut self, fn_def: GlobalNodeId, callee_ty: TypeId, genv: &GenericEnv) -> Value {
        let callee_ty = self.normalized(callee_ty);

        let genv_vars = self.resolve_fn_genv_vars(callee_ty, genv);
        let genv_id = self.make_genv_id(&genv_vars, genv);

        let mid = (fn_def, genv_id);
        if let Some(&v) = self.fn_decls.get(&mid) {
            return v.ll.direct();
        }

        let package = &self.packages[fn_def.0];
        let name = if package.check_data.entry_point() == Some(callee_ty) {
            "__main"
        } else {
            package.hir.fn_def(fn_def.1).name.value.as_str()
        };
        let ty = self.packages.type_(callee_ty);
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

            let body_bb = self.llvm.append_new_bb(fn_, "body");
            self.bodyb.position_at_end(body_bb);

            for (i, &param) in params.iter().enumerate() {
                let name = &package.hir.fn_def_param(param).name.value;
                let val = self.alloca(param, name, ctx);
                let param = fn_.param(i as u32);
                self.bodyb.store(param, val.ptr());
            }

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
                let tmp = self.alloca_new_ty(v.type_(), "", ctx).ptr();
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
                let receiver = self.make_ptr(receiver, ctx).into();
                let idx = ctx.package.check_data.struct_field_index(node);
                self.bodyb.struct_gep(receiver, idx).indirect()
            }
            NodeKind::FnCall => {
                let fnc = ctx.package.hir.fn_call(node);
                let callee_ty = ctx.package.check_data.typing(fnc.callee);
                let callee = self.expr(fnc.callee, ctx);
                let args = fnc.args.iter()
                    .map(|v| self.expr(v.value, ctx))
                    .collect::<Vec<_>>();
                self.fn_call(node, callee_ty, callee, &args, ctx)
            }
            NodeKind::Let => {
                let &Let { def } = ctx.package.hir.let_(node);

                let &LetDef { init, .. } = ctx.package.hir.let_def(def);
                let p = self.expr(def, ctx).ptr();

                if let Some(init) = init {
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
                if let Some(OpImpl { fn_def, callee_ty, lvalue_result }) = ctx.package.check_data.op_impl(node) {
                    let callee = self.fn_def(fn_def, callee_ty, ctx.genv);
                    let r = match ctx.package.hir.op(node) {
                        &Op::Binary(BinaryOp { kind: _, left, right }) => {
                            let left = self.expr(left, ctx);
                            let right = self.expr(right, ctx);
                            self.fn_call(node, callee_ty, callee, &[left, right], ctx)
                        }
                        &Op::Unary(UnaryOp { kind: _, arg }) => {
                            let arg = self.expr(arg, ctx);
                            self.fn_call(node, callee_ty, callee, &[arg], ctx)
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
                                        self.div_or_rem(ctx, left_ty, rightv,
                                            || self.bodyb.sdiv(leftv, rightv),
                                            || self.bodyb.udiv(leftv, rightv),
                                            || self.bodyb.fdiv(leftv, rightv))
                                    },
                                    Rem => {
                                        self.div_or_rem(ctx, left_ty, rightv,
                                            || self.bodyb.srem(leftv, rightv),
                                            || self.bodyb.urem(leftv, rightv),
                                            || self.bodyb.frem(leftv, rightv))
                                    },
                                    Index => unreachable!(),

                                    _ => todo!("{:?}", kind)
                                }
                            }
                        },
                        &Op::Unary(UnaryOp { kind, arg }) => {
                            let argv = self.expr(arg, ctx).deref(self.bodyb);
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
            NodeKind::SliceLiteral => {
                let ty = self.normalized(self.packages.typing((ctx.package.id, node)));
                let ty = self.packages.type_(ty).data.as_slice().unwrap();

                let SliceLiteral { items, len } = ctx.package.hir.slice_literal(node);
                let len_val = if let Some(v) = len.value {
                    if len.const_ {
                        self.llvm.size_type().const_int(ty.len.unwrap() as u128)
                    } else {
                        assert_eq!(items.len(), 1);
                        self.expr(v, ctx).deref(self.bodyb)
                    }
                } else {
                    self.llvm.size_type().const_int(items.len() as u128)
                };

                let item_ty = self.type_(ty.item, ctx.genv);

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
                    let item_val = self.expr(items[0], ctx).deref(self.bodyb);

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
                        let item_val = self.expr(item, ctx).deref(self.bodyb);
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
                    let ty = self.type_(ty, ctx.genv);
                    ty.const_struct(&mut []).direct()
                } else {
                    let struct_var = self.alloca(node, "struct_literal", ctx);
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
        ctx: &ExprCtx,
        left_ty: TypeId,
        rightv: ValueRef,
        make_signed: impl FnOnce() -> ValueRef,
        make_unsigned: impl FnOnce() -> ValueRef,
        make_float: impl FnOnce() -> ValueRef,
    ) -> Value {
        match self.packages.as_number(left_ty).expect("todo") {
            NumberType::Float => make_float(),
            NumberType::Int { signed } => {
                let cond = self.bodyb.icmp(rightv, rightv.type_().const_int(0), IntPredicate::LLVMIntEQ);
                self.panic_if(cond, ctx);
                if signed {
                    make_signed()
                } else {
                    make_unsigned()
                }
            },
        }.direct()
    }

    fn panic_if(&self, cond: ValueRef, ctx: &ExprCtx) {
        let panic_bb = self.llvm.append_new_bb(ctx.fn_, "__panic");
        let succ_bb = self.llvm.append_new_bb(ctx.fn_, "__panic_succ");
        self.bodyb.cond_br(cond, panic_bb, succ_bb);

        self.bodyb.position_at_end(panic_bb);
        intrinsic::trap(&self.llvm, self.bodyb);
        self.bodyb.unreachable();

        self.bodyb.position_at_end(succ_bb);
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
            TypeData::Slice(v) => self.make_slice_type(v, genv),
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
                return self.make_prim_type(ty, prim, genv);
            }
        }
        let field_tys = &mut Vec::with_capacity(fields.len());
        for &check::StructTypeField { name: _, ty } in fields {
            field_tys.push(self.type_(ty, genv));
        }
        self.make_struct_type0(*def, field_tys)
    }

    fn make_slice_type(&mut self, slt: &check::SliceType, genv: &GenericEnv) -> TypeRef {
        let &check::SliceType { item, len } = slt;
        let item = self.type_(item, genv);
        if let Some(len) = len {
            self.llvm.array_type(item, len)
        } else {
            self.llvm.struct_type(&mut [
                self.llvm.pointer_type(item),
                self.llvm.size_type(),
            ])
        }
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

    fn make_prim_type(&mut self, ty: TypeId, prim_ty: PrimitiveType, genv: &GenericEnv) -> TypeRef {
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
            ISize | USize => self.llvm.size_type(),
            Ptr => {
                let pty = self.packages.type_(ty).data.as_generic_env().unwrap().vars.vals().next().unwrap();
                let pty = self.type_(pty, genv);
                pty.pointer()
            }
        }
    }

    fn lang_type(&mut self, lang_item: LangItem) -> TypeRef {
        self.type_(self.packages.std().check_data.lang().type_(lang_item), &self.default_genv())
    }

    fn alloca(&mut self, node: NodeId, name: &str, ctx: &mut ExprCtx) -> Value {
        if ctx.allocas.contains_key(&node) {
            ctx.allocas[&node]
        } else {
            let r = self.alloca_new(node, name, ctx);
            assert!(ctx.allocas.insert(node, r).is_none());
            r
        }
    }

    fn alloca_new(&mut self, node: NodeId, name: &str, ctx: &mut ExprCtx) -> Value {
        let ty = ctx.package.check_data.typing(node);
        let ty = self.normalized(ty);
        let ty_ll = self.type_(ty, ctx.genv);

        if let &TypeData::Slice(check::SliceType { item, len: Some(len) }) = &self.packages.underlying_type(ty).data {
            let slot_ty = ty_ll.pointer();
            let slot = self.alloca_new_ty(slot_ty, name, ctx).ptr();
            let item_ty = self.type_(item, ctx.genv);
            let ptr = self.gc_malloc(item_ty, self.llvm.size_type().const_int(len as u128), node, ctx);
            let ptr = self.bodyb.bitcast(ptr, slot_ty);
            self.bodyb.store(ptr, slot);
            ptr.indirect()
        } else {
            self.alloca_new_ty(ty_ll, name, ctx)
        }
    }

    fn alloca_new_ty(&mut self, ty: TypeRef, name: &str, ctx: &mut ExprCtx) -> Value {
        ctx.alloca_count += 1;
        self.headerb.position_at_end(ctx.fn_.entry_bb());
        self.headerb.alloca(name, ty).indirect()
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

    fn fn_call(&mut self, node: NodeId, callee_ty: TypeId, callee: Value, args: &[Value], ctx: &mut ExprCtx) -> Value {
        let callee_ty = self.normalized(callee_ty);
        let intrinsic = self.packages.as_lang_item(callee_ty)
            .and_then(|v| v.into_intrinsic().ok());
        if let Some(intr) = intrinsic {
            match intr {
                IntrinsicItem::Trap => {
                    assert!(args.is_empty());
                    intrinsic::trap(&self.llvm, self.bodyb);
                    self.unit_literal()
                }
                IntrinsicItem::Transmute => {
                    assert_eq!(args.len(), 1);
                    let src = args[0];
                    let src = self.make_ptr(src, ctx);
                    let src_size = self.llvm.abi_size_bytes(src.type_().inner());

                    let dst_ty = self.packages.underlying_type(callee_ty).data.as_fn().unwrap().result;
                    let dst_ty = self.type_(dst_ty, ctx.genv);
                    let dst_size = self.llvm.abi_size_bytes(dst_ty);

                    if src_size != dst_size {
                        todo!("must fail in frontend");
                    }

                    let dst = self.alloca_new_ty(dst_ty, "", ctx);

                    let i8ptr = self.llvm.int_type(8).pointer();
                    let src_ptr = self.bodyb.bitcast(src, i8ptr);
                    let dst_ptr = self.bodyb.bitcast(dst.ptr(), i8ptr);
                    let len = match self.llvm.pointer_size_bits() {
                        32 => self.llvm.int_type(32),
                        64 => self.llvm.int_type(64),
                        _ => unreachable!(),
                    }.const_int(src_size as u128);
                    intrinsic::memcpy(&self.llvm, self.bodyb, dst_ptr, src_ptr, len,
                        self.llvm.int_type(1).const_int(0));

                    dst
                }
            }
        } else {
            let mut args = args.to_vec();
            if let Some(slice_ty) = ctx.package.check_data.method_call_self_coercion(node) {
                // [T; N] -> [T]
                let arr = self.make_ptr(args[0], ctx);
                let arr_ty = arr.type_().inner();
                let item_ty = arr_ty.inner();
                let len = arr_ty.array_len();

                debug_assert!(matches!(self.packages.underlying_type(slice_ty).data, TypeData::Slice(_)));
                let slice_ty = self.type_(slice_ty, ctx.genv);

                let slice_var = self.alloca_new_ty(slice_ty, "slice_coercion", ctx).ptr();
                let ptr = self.bodyb.bitcast(arr, item_ty.pointer());
                self.bodyb.store(ptr, self.bodyb.struct_gep(slice_var, 0));
                self.bodyb.store(self.llvm.size_type().const_int(len as u128), self.bodyb.struct_gep(slice_var, 1));

                args[0] = slice_var.indirect();
            };

            let mut args: Vec<_> = args.into_iter()
                .map(|v| v.deref(self.bodyb))
                .collect();
            let callee = callee.deref(self.bodyb);
            self.bodyb.call(callee, &mut args).direct()
        }
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