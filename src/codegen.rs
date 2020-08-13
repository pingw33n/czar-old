use llvm_sys::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
use std::collections::{HashMap, HashSet};
use std::ffi::{CStr, CString};
use std::ptr::{self, NonNull};
use std::sync::Once;

use crate::hir::*;
use crate::package::{Package, Packages, GlobalNodeId, PackageId};
use crate::semantic::type_check::*;
use crate::syntax::*;

#[derive(Clone, Copy, Debug)]
pub enum OutputFileKind {
    Assembly,
    Object,
}

static INIT: Once = Once::new();

#[derive(Clone, Copy)]
struct ExprCtx<'a> {
    package: &'a Package,
    fn_ll: NonNull<LLVMValue>,
    allocas: &'a HashMap<NodeId, NonNull<LLVMValue>>,
    rvalue: bool,
}

impl ExprCtx<'_> {
    pub fn lvalue(mut self) -> Self {
        self.rvalue = false;
        self
    }
}

pub struct Codegen<'a> {
    ctx: LLVMContextRef,
    module: LLVMModuleRef,
    bld: LLVMBuilderRef,
    target_machine: LLVMTargetMachineRef,
    data_layout: LLVMTargetDataRef,
    packages: &'a Packages,
    fn_decls: HashMap<GlobalNodeId, NonNull<LLVMValue>>,
    fn_body_todos: HashSet<GlobalNodeId>,
    types: HashMap<TypeId, NonNull<LLVMType>>,
}

impl<'a> Codegen<'a> {
    pub fn new(packages: &'a Packages) -> Self {
        INIT.call_once(|| {
            unsafe {
                measure_time::print_time!("init LLVM targets");
                LLVM_InitializeAllTargetInfos();
                LLVM_InitializeAllTargets();
                LLVM_InitializeAllTargetMCs();
                LLVM_InitializeAllAsmParsers();
                LLVM_InitializeAllAsmPrinters();
            }
        });
        let ctx;
        let module;
        let bld;
        let target_machine;
        let data_layout;
        unsafe {
            ctx = LLVMContextCreate();
            assert!(!ctx.is_null());

            module = LLVMModuleCreateWithNameInContext(b"codegen\0".as_ptr() as *const _, ctx);
            assert!(!module.is_null());

            bld = LLVMCreateBuilderInContext(ctx);
            assert!(!bld.is_null());

            let triple = LLVMGetDefaultTargetTriple();
            let mut target = ptr::null_mut();
            let mut error = ptr::null_mut();
            assert_eq!(LLVMGetTargetFromTriple(triple, &mut target, &mut error), 0,
                "{}", CStr::from_ptr(error).to_string_lossy());
            target_machine = LLVMCreateTargetMachine(
                target, triple, empty_cstr(), empty_cstr(),
                LLVMCodeGenOptLevel::LLVMCodeGenLevelAggressive,
                LLVMRelocMode::LLVMRelocDefault, LLVMCodeModel::LLVMCodeModelDefault);
            assert!(!target_machine.is_null());

            LLVMSetTarget(module, triple);
            LLVMDisposeMessage(triple);

            data_layout = LLVMCreateTargetDataLayout(target_machine);
            assert!(!data_layout.is_null());
            LLVMSetModuleDataLayout(module, data_layout);
        }
        Self {
            ctx,
            module,
            bld,
            target_machine,
            data_layout,
            packages,
            fn_decls: HashMap::new(),
            fn_body_todos: HashSet::new(),
            types: HashMap::new(),
        }
    }

    pub fn run(&mut self, package_id: PackageId) {
        let entry_point = self.packages[package_id].resolve_data.entry_point().unwrap();

        self.fn_decl((package_id, entry_point));

        while let Some(&node) = self.fn_body_todos.iter().next() {
            self.fn_body(node);
            assert!(self.fn_body_todos.remove(&node));
        }
    }

    fn fn_decl(&mut self, node: GlobalNodeId) -> NonNull<LLVMValue> {
        if let Some(&v) = self.fn_decls.get(&node) {
            return v;
        }

        let ty = self.typing(node);

        let package = &self.packages[node.0];
        let name = if package.resolve_data.entry_point() == Some(node.1) {
            "__main"
        } else {
            package.hir.fn_decl(node.1).name.value.as_str()
        };
        let name = CString::new(name).unwrap();
        let func = NonNull::new(unsafe {
            LLVMAddFunction(self.module, name.as_ptr(), ty.as_ptr())
        }).unwrap();

        assert!(self.fn_decls.insert(node, func).is_none());
        assert!(self.fn_body_todos.insert(node));

        func
    }

    fn fn_body(&mut self, fn_decl: GlobalNodeId) {
        let package = &self.packages[fn_decl.0];
        let FnDecl { args, body, .. } = package.hir.fn_decl(fn_decl.1);
        if let Some(body) = *body {
            let fn_ll = self.fn_decls[&fn_decl];
            unsafe {
                let bb = NonNull::new(LLVMAppendBasicBlockInContext(
                    self.ctx, fn_ll.as_ptr(), b"entry\0".as_ptr() as *const _)).unwrap();
                LLVMPositionBuilderAtEnd(self.bld, bb.as_ptr());
            };

            let allocas = &mut HashMap::new();

            for &node in package.discover_data.fn_allocas(fn_decl.1) {
                let name = match package.hir.node_kind(node).value {
                    NodeKind::IfExpr => "",
                    NodeKind::LetDecl => package.hir.let_decl(node).name.value.as_str(),
                    _ => unreachable!()
                };
                let ty = package.types.typing(node);
                let ll_ty = self.type_(ty);
                let val = NonNull::new(unsafe {
                    LLVMBuildAlloca(self.bld, ll_ty.as_ptr(), cstring(name).as_ptr())
                }).unwrap();
                assert!(allocas.insert(node, val).is_none());
            }

            for (i, &arg) in args.iter().enumerate() {
                let name = &package.hir.fn_decl_arg(arg).priv_name.value;
                let param = NonNull::new(unsafe { LLVMGetParam(fn_ll.as_ptr(), i as u32) }).unwrap();
                let val = NonNull::new(unsafe {
                    LLVMBuildAlloca(self.bld, LLVMTypeOf(param.as_ptr()), cstring(name).as_ptr())
                }).unwrap();
                self.build_store(param, val);
                assert!(allocas.insert(arg, val).is_none());
            }

            let ret = self.expr(body, &mut ExprCtx {
                package,
                fn_ll,
                allocas,
                rvalue: true,
            });
            NonNull::new(unsafe { LLVMBuildRet(self.bld, ret.as_ptr()) }).unwrap();
        }
    }

    fn build_load(&self, v: NonNull<LLVMValue>) -> NonNull<LLVMValue> {
        NonNull::new(unsafe { LLVMBuildLoad(self.bld, v.as_ptr(), empty_cstr()) }).unwrap()
    }

    fn build_store(&self, val: NonNull<LLVMValue>, ptr: NonNull<LLVMValue>) {
        NonNull::new(unsafe { LLVMBuildStore(self.bld, val.as_ptr(), ptr.as_ptr()) }).unwrap();
    }

    fn append_and_attach_bb(&self, fn_: NonNull<LLVMValue>, bb: NonNull<LLVMBasicBlock>) {
        unsafe {
            LLVMAppendExistingBasicBlock(fn_.as_ptr(), bb.as_ptr());
            LLVMPositionBuilderAtEnd(self.bld, bb.as_ptr());
        }
    }

    fn expr(&mut self, node: NodeId, ctx: &mut ExprCtx) -> NonNull<LLVMValue> {
        match ctx.package.hir.node_kind(node).value {
            NodeKind::Block => {
                let Block { exprs } = ctx.package.hir.block(node);
                let mut r = None;
                for &expr in exprs {
                    r = Some(self.expr(expr, ctx));
                }
                r.unwrap_or_else(|| self.unit_literal())
            }
            NodeKind::FnCall => {
                let FnCall { callee, kind, args } = ctx.package.hir.fn_call(node);
                if *kind != FnCallKind::Free {
                    todo!();
                }
                let callee = self.expr(*callee, ctx);
                let mut args_ll = Vec::new();
                for &FnCallArg { value, .. } in args {
                    let v = self.expr(value, ctx);
                    args_ll.push(v);
                }
                NonNull::new(unsafe { LLVMBuildCall(
                    self.bld,
                    callee.as_ptr(),
                    args_ll.as_mut_ptr() as *mut _,
                    args_ll.len() as u32,
                    empty_cstr())
                }).unwrap()
            }
            NodeKind::FnDecl => {
                self.fn_decl((ctx.package.id, node))
            }
            NodeKind::Let => {
                let &Let { decl } = ctx.package.hir.let_(node);

                let &LetDecl { init, .. } = ctx.package.hir.let_decl(decl);

                if let Some(init) = init {
                    let p = self.expr(decl, &mut ctx.lvalue());
                    let v = self.expr(init, ctx);
                    self.build_store(v, p);
                }

                self.bool_literal(true)
            }
            NodeKind::IfExpr => {
                let &IfExpr { cond, if_true, if_false } = ctx.package.hir.if_expr(node);
                let cond = self.expr(cond, ctx);
                let if_true_bb = NonNull::new(unsafe { LLVMCreateBasicBlockInContext(self.ctx, cstring("bb_if_true").as_ptr()) }).unwrap();
                let if_false_bb = NonNull::new(unsafe { LLVMCreateBasicBlockInContext(self.ctx, cstring("bb_if_false").as_ptr()) }).unwrap();
                let succ_bb = NonNull::new(unsafe { LLVMCreateBasicBlockInContext(self.ctx, cstring("bb_if_succ").as_ptr()) }).unwrap();
                NonNull::new(unsafe { LLVMBuildCondBr(self.bld, cond.as_ptr(), if_true_bb.as_ptr(), if_false_bb.as_ptr())}).unwrap();

                let ret_var = ctx.allocas[&node];

                self.append_and_attach_bb(ctx.fn_ll, if_true_bb);
                let v = self.expr(if_true, ctx);
                self.build_store(v, ret_var);
                NonNull::new(unsafe { LLVMBuildBr(self.bld, succ_bb.as_ptr()) }).unwrap();

                self.append_and_attach_bb(ctx.fn_ll, if_false_bb);
                if let Some(if_false) = if_false {
                    let v = self.expr(if_false, ctx);
                    self.build_store(v, ret_var);
                }
                NonNull::new(unsafe { LLVMBuildBr(self.bld, succ_bb.as_ptr()) }).unwrap();

                self.append_and_attach_bb(ctx.fn_ll, succ_bb);

                self.build_load(ret_var)
            }
            NodeKind::FnDeclArg | NodeKind::LetDecl => {
                let v = ctx.allocas[&node];
                if ctx.rvalue {
                    self.build_load(v)
                } else {
                    v
                }
            }
            NodeKind::Literal => {
                let lit = ctx.package.hir.literal(node);
                match lit {
                    &Literal::Bool(v) => self.bool_literal(v),
                    Literal::Char(_) => todo!(),
                    Literal::String(_) => todo!(),
                    &Literal::Int(IntLiteral { value, .. }) => {
                        let ty = self.typing((ctx.package.id, node));
                        NonNull::new(unsafe { LLVMConstIntOfArbitraryPrecision(ty.as_ptr(), 2, [value as u64, (value >> 64) as u64].as_ptr()) }).unwrap()
                    },
                    Literal::Float(_) => todo!(),
                    Literal::Unit => self.unit_literal(),
                }
            }
            NodeKind::Op => {
                let op = ctx.package.hir.op(node);
                match op {
                    &Op::Binary(BinaryOp { kind, left, right }) => {
                        let left = self.expr(left, ctx);
                        let right = self.expr(right, ctx);
                        use BinaryOpKind::*;
                        match kind.value {
                            Add => {
                                NonNull::new(unsafe { LLVMBuildAdd(self.bld, left.as_ptr(), right.as_ptr(), empty_cstr())}).unwrap()
                            },
                            LtEq => {
                                NonNull::new(unsafe { LLVMBuildICmp(self.bld, LLVMIntPredicate::LLVMIntSLE, left.as_ptr(), right.as_ptr(), empty_cstr())}).unwrap()
                            },
                            Sub => {
                                NonNull::new(unsafe { LLVMBuildSub(self.bld, left.as_ptr(), right.as_ptr(), empty_cstr())}).unwrap()
                            },
                            _ => todo!("{:?}", kind)
                        }
                    },
                    &Op::Unary(UnaryOp { kind, arg }) => {
                        todo!()
                    },
                }
            }
            NodeKind::Path => {
                let reso = ctx.package.types.target_of(node);
                if reso.0 == ctx.package.id {
                    self.expr(reso.1, ctx)
                } else {
                    let package = &self.packages[reso.0];
                    self.expr(reso.1, &mut ExprCtx {
                        package,
                        fn_ll: ctx.fn_ll,
                        allocas: ctx.allocas,
                        rvalue: ctx.rvalue,
                    })
                }
            }
            NodeKind::StructValue => {
                let StructValue { name, anonymous_fields, fields } = ctx.package.hir.struct_value(node);
                if !(name.is_none() && anonymous_fields.is_none() && fields.is_empty()) {
                    todo!();
                }
                self.unit_literal()
            }
            _ => todo!("{:?}", ctx.package.hir.node_kind(node))
        }
    }

    fn bool_literal(&mut self, v: bool) -> NonNull<LLVMValue> {
        let ty = self.type_((PackageId::std(), self.packages[PackageId::std()].types.lang(LangType::Bool)));
        let v = if v { 1 } else { 0 };
        NonNull::new(unsafe { LLVMConstInt(ty.as_ptr(), v, 0) }).unwrap()
    }

    fn unit_literal(&self) -> NonNull<LLVMValue> {
        NonNull::new(unsafe { LLVMConstStructInContext(self.ctx, ptr::null_mut(), 0, 0) }).unwrap()
    }

    fn unalias(&self, ty: TypeId) -> TypeId {
        if let &TypeData::Type(ty) = self.packages[ty.0].types.type_(ty.1).data() {
            self.unalias(ty)
        } else {
            ty
        }
    }

    fn typing(&mut self, node: GlobalNodeId) -> NonNull<LLVMType> {
        let ty = self.packages[node.0].types.typing(node.1);
        self.type_(ty)
    }

    fn type_(&mut self, ty: TypeId) -> NonNull<LLVMType> {
        if let Some(&v) = self.types.get(&ty) {
            return v;
        }
        let unaliased = self.unalias(ty);
        let ll_ty = match self.packages[unaliased.0].types.type_(unaliased.1).data() {
            TypeData::Fn(FnType { args, result, .. }) => {
                let mut args_ty = Vec::with_capacity(args.len());
                for &arg in args {
                    args_ty.push(self.type_(arg));
                }
                let res_ty = self.type_(*result);
                unsafe {
                    LLVMFunctionType(res_ty.as_ptr(), args_ty.as_mut_ptr() as *mut _, args_ty.len() as u32, 0)
                }
            }
            &TypeData::Primitive(prim) => match prim {
                PrimitiveType::Bool => unsafe { LLVMInt1TypeInContext(self.ctx) },
                PrimitiveType::I32 => unsafe { LLVMInt32TypeInContext(self.ctx) },
                PrimitiveType::Unit => unsafe { LLVMStructTypeInContext(self.ctx, ptr::null_mut(), 0, 0) },
            }
            _ => todo!(),
        };
        let ll_ty = NonNull::new(ll_ty).unwrap();

        assert!(self.types.insert(ty, ll_ty).is_none());
        if unaliased != ty {
            assert!(self.types.insert(unaliased, ll_ty).is_none());
        }

        ll_ty
    }

    pub fn dump(&self) {
        unsafe { LLVMDumpModule(self.module); }
    }

    pub fn write(&self, path: impl AsRef<std::path::Path>, output_kind: OutputFileKind) {
        unsafe {
            let filename = path_to_c_string(path.as_ref());
            let mut error = ptr::null_mut();
            let ft = match output_kind {
                OutputFileKind::Assembly => LLVMCodeGenFileType::LLVMAssemblyFile,
                OutputFileKind::Object => LLVMCodeGenFileType::LLVMObjectFile,
            };
            let r = LLVMTargetMachineEmitToFile(
                self.target_machine,
                self.module,
                filename.as_ptr() as *mut _,
                ft,
                &mut error);
            assert_eq!(r, 0, "{}", CStr::from_ptr(error).to_string_lossy());
        }
    }
}

impl Drop for Codegen<'_> {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeBuilder(self.bld);
            LLVMContextDispose(self.ctx);
            LLVMDisposeTargetMachine(self.target_machine);
        }
    }
}

fn cstring(s: &str) -> CString {
    CString::new(s.as_bytes().to_vec()).unwrap()
}

fn empty_cstr() -> *const i8 {
    "\0".as_ptr() as *const _
}

#[cfg(unix)]
fn path_to_c_string(p: &std::path::Path) -> CString {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;
    let p: &OsStr = p.as_ref();
    CString::new(p.as_bytes()).unwrap()
}

#[cfg(windows)]
fn path_to_c_string(p: &PathExpr) -> CString {
    CString::new(p.to_str().unwrap()).unwrap()
}