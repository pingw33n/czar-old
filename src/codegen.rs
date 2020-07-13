use enum_as_inner::EnumAsInner;
use llvm_sys::*;
use llvm_sys::core::*;
use llvm_sys::prelude::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
use std::ffi::{CStr, CString};
use std::ptr;

use crate::syn::*;
use std::ptr::NonNull;
use std::sync::Once;
use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub enum OutputFileKind {
    Assembly,
    Object,
}

#[derive(Debug, EnumAsInner)]
enum Value {
    Void,
    Value(NonNull<LLVMValue>),
}

impl Value {
    fn dump(&self) {
        match self {
            Self::Void => eprintln!("<Void>"),
            Self::Value(v) => {
                unsafe { LLVMDumpValue(v.as_ptr()); }
                eprintln!();
            }
        }
    }
}

impl From<LLVMValueRef> for Value {
    fn from(v: *mut LLVMValue) -> Self {
        Self::Value(NonNull::new(v).unwrap())
    }
}

static INIT: Once = Once::new();

pub struct Codegen<'a> {
    context: LLVMContextRef,
    module: LLVMModuleRef,
    builder: LLVMBuilderRef,
    target_machine: LLVMTargetMachineRef,
    data_layout: LLVMTargetDataRef,
    ast: &'a Ast,
}

impl<'a> Codegen<'a> {
    pub fn new(ast: &'a Ast) -> Self {
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
        let context;
        let module;
        let builder;
        let target_machine;
        let data_layout;
        unsafe {
            context = LLVMContextCreate();
            assert!(!context.is_null());

            module = LLVMModuleCreateWithNameInContext(b"codegen\0".as_ptr() as *const _, context);
            assert!(!module.is_null());

            builder = LLVMCreateBuilderInContext(context);
            assert!(!builder.is_null());

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
            context,
            module,
            builder,
            target_machine,
            data_layout,
            ast,
        }
    }

    pub fn lower(&mut self) {
        self.module(self.ast.module_decl(self.ast.root.value));
    }

    fn module(&mut self, module_decl: &ModuleDecl) {
        for item in &module_decl.items {
            let id = item.value;
            match self.ast.node_kind(id) {
                NodeKind::FnDecl => {
                    self.func(self.ast.fn_decl(id));
                }
                NodeKind::ModuleDecl => {
                    self.module(self.ast.module_decl(id));
                }
                NodeKind::StructDecl => unimplemented!(),
                NodeKind::UseStmt => unimplemented!(),
                | NodeKind::Block
                | NodeKind::Cast
                | NodeKind::Empty
                | NodeKind::FieldAccess
                | NodeKind::FnCall
                | NodeKind::Literal
                | NodeKind::Op
                | NodeKind::SymPath
                | NodeKind::TyExpr
                | NodeKind::UsePath
                | NodeKind::VarDecl
                => unreachable!(),
            }
        }
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

    fn func(&mut self, fn_decl: &FnDecl) {
        let ret_ty = if let Some(ty) = fn_decl.ret_ty {
            self.ty(ty.value)
        } else {
            self.ty_void()
        };
        let mut args_ty = Vec::with_capacity(fn_decl.args.len());
        for arg in &fn_decl.args {
            args_ty.push(self.ty(arg.ty.value));
        }
        let func_ty = unsafe {
            LLVMFunctionType(ret_ty, args_ty.as_mut_ptr(), args_ty.len() as u32, 0)
        };
        assert!(!func_ty.is_null());

        let name = CString::new(fn_decl.name.value.clone()).unwrap();
        let func = unsafe {
            LLVMAddFunction(self.module, name.as_ptr(), func_ty)
        };
        assert!(!func.is_null());

        if let Some(body) = fn_decl.body.as_ref() {
            unsafe {
                let bb = LLVMAppendBasicBlockInContext(self.context, func,
                    b"entry\0".as_ptr() as *const _);
                assert!(!bb.is_null());
                LLVMPositionBuilderAtEnd(self.builder, bb);
            };
            let ctx = &mut ExprCtx { func, fn_decl, vars: vec![HashMap::new()] };

            for i in 0..fn_decl.args.len() {
                let param = unsafe { LLVMGetParam(ctx.func, i as u32) };
                ctx.vars.last_mut().unwrap().insert(fn_decl.args[i].name.value.clone(), param);
            }

            let ret = self.block(body.value, ctx);
            match ret {
                Value::Void => unsafe { LLVMBuildRetVoid(self.builder); }
                Value::Value(ret) => unsafe { LLVMBuildRet(self.builder,ret.as_ptr()); }
            }
        }
    }

    fn expr(&self, node: NodeId, ctx: &mut ExprCtx) -> Value {
        match self.ast.node_kind(node) {
            NodeKind::VarDecl => {
                let VarDecl { muta: _, name, ty, init } = self.ast.var_decl(node);
                unsafe {
                    let ty = self.ty(ty.as_ref().expect("unimpl").value);
                    let ptr = LLVMBuildAlloca(self.builder, ty, cstring(&name.value).as_ptr());

                    let init = init.expect("unimpl").value;
                    let init = self.expr(init, ctx).into_value().unwrap();

                    LLVMBuildStore(self.builder, init.as_ptr(), ptr);

                    ctx.vars.last_mut().unwrap().insert(name.value.clone(), ptr);

                    Value::Void
                }
            }
            NodeKind::Cast => {
                let Cast { expr, ty } = self.ast.cast(node);
                let v = self.expr(expr.value, ctx);
                if v.as_void().is_some() {
                    return Value::Void;
                }
                let ty = self.ty(ty.value);
                v.dump();
                unsafe {
                    println!();
                    LLVMDumpType(ty);
                    println!();
                    LLVMBuildBitCast(self.builder, v.as_value().unwrap().as_ptr(), ty, empty_cstr()).into()
                }
            }
            NodeKind::Literal => {
                let lit = self.ast.literal(node);
                match lit {
                    &Literal::Int(v) => unsafe {
                        let ty = match v.ty.unwrap() {
                            IntTypeSuffix::I8 | IntTypeSuffix::U8 => LLVMInt8TypeInContext(self.context),
                            IntTypeSuffix::I16 | IntTypeSuffix::U16 => LLVMInt16TypeInContext(self.context),
                            IntTypeSuffix::I32 | IntTypeSuffix::U32 => LLVMInt32TypeInContext(self.context),
                            IntTypeSuffix::I64 | IntTypeSuffix::U64 => LLVMInt64TypeInContext(self.context),
                            IntTypeSuffix::I128 | IntTypeSuffix::U128 => LLVMInt128TypeInContext(self.context),
                            IntTypeSuffix::Isize | IntTypeSuffix::Usize => LLVMIntType(self.isize_len_bytes() * 8),
                        };
                        LLVMConstIntOfArbitraryPrecision(ty, 2, [v.value as u64, (v.value >> 64) as u64].as_ptr()).into()
                    }
                    &Literal::Float(v) => unsafe {
                        let ty = match v.ty.unwrap() {
                            FloatTypeSuffix::F32 => LLVMFloatTypeInContext(self.context),
                            FloatTypeSuffix::F64 => LLVMDoubleTypeInContext(self.context),
                        };
                        LLVMConstReal(ty, v.value).into()
                    }
                    Literal::String(s) => unsafe {
                        // let mut el_tys = [
                        //     LLVMPointerType(LLVMInt8TypeInContext(self.context), 0),
                        //     LLVMInt64TypeInContext(self.context),
                        // ];
                        // let ty = LLVMStructTypeInContext(self.context, el_tys.as_mut_ptr(), 2, 1);
                        // assert!(!ty.is_null());

                        let s_const = LLVMConstStringInContext(self.context, s.as_ptr() as *const _, s.len() as u32, 1);
                        // let len = LLVMConstInt(LLVMInt64TypeInContext(self.context), s.len() as u64, 0);
                        // let stru = LLVMConstStructInContext(self.context, [s_const, len].as_mut_ptr(), 2, 1);
                        // assert!(!stru.is_null());

                        let g = LLVMAddGlobal(self.module, LLVMTypeOf(s_const), empty_cstr());
                        LLVMSetGlobalConstant(g, 1);
                        LLVMSetInitializer(g, s_const);
                        LLVMSetUnnamedAddress(g, LLVMUnnamedAddr::LLVMGlobalUnnamedAddr);
                        LLVMSetLinkage(g, LLVMLinkage::LLVMLinkerPrivateLinkage);
                        g.into()
                    }
                    &Literal::Char(v) => unsafe {
                        LLVMConstInt(LLVMInt32TypeInContext(self.context), v as u64, 0).into()
                    }
                    &Literal::Bool(v) => unsafe {
                        LLVMConstInt(LLVMInt8TypeInContext(self.context), v as u64, 0).into()
                    }
                }
            }
            NodeKind::Op => {
                match self.ast.op(node) {
                    Op::BinaryOp(op) => {
                        let l = self.expr(op.left.value, ctx).into_value().unwrap();
                        let r = self.expr(op.right.value, ctx).into_value().unwrap();
                        match op.kind.value {
                            BinaryOpKind::Add => {
                                unsafe {
                                    LLVMBuildAdd(self.builder, l.as_ptr(), r.as_ptr(), empty_cstr())
                                }
                            }
                            BinaryOpKind::Div => {
                                unimplemented!();
                                unsafe {
                                    LLVMBuildSDiv(self.builder, l.as_ptr(), r.as_ptr(), empty_cstr())
                                }
                            }
                            BinaryOpKind::Mul => {
                                unsafe {
                                    LLVMBuildMul(self.builder, l.as_ptr(), r.as_ptr(), empty_cstr())
                                }
                            }
                            BinaryOpKind::Sub => {
                                unsafe {
                                    LLVMBuildSub(self.builder, l.as_ptr(), r.as_ptr(), empty_cstr())
                                }
                            }
                        }
                    }
                    Op::Unary(op) => {
                        let arg = self.expr(op.arg.value, ctx).into_value().unwrap();
                        match op.kind.value {
                            UnaryOpKind::Neg => {
                                unsafe {
                                    LLVMBuildNeg(self.builder, arg.as_ptr(), empty_cstr())
                                }
                            }
                        }
                    }
                }.into()
            }
            NodeKind::FnCall => {
                let fn_call = self.ast.fn_call(node);
                match &fn_call.callee.value {
                    FnCallee::Intrinsic(intr) => {
                        assert_eq!(fn_call.kind, FnCallKind::Free);
                        match intr {
                            Intrinsic::OverflowingAdd => unimplemented!()
                        }
                    }
                    &FnCallee::Expr(expr) => {
                        let callee = self.expr(expr, ctx).into_value().unwrap().as_ptr();
                        let mut args = Vec::with_capacity(fn_call.args.len());
                        for a in &fn_call.args {
                            let v = self.expr(a.value, ctx);
                            v.dump();
                            if let Value::Value(v) = v {
                                args.push(v.as_ptr());
                            }
                        }
                        unsafe {
                            let ty = LLVMGlobalGetValueType(callee);
                            // dbg!(LLVMGetTypeKind(LLVMGetParam(f, 0)));
                        }
                        unsafe {
                            let r = LLVMBuildCall(self.builder, callee, args.as_mut_ptr(), args.len() as u32, empty_cstr());
                            r.into()
                        }
                    }
                }
            }
            NodeKind::SymPath => unimplemented!(),
            NodeKind::UseStmt => unimplemented!(),
            NodeKind::UsePath => unreachable!(),
            NodeKind::Empty => Value::Void,
            //     {
            //     let path = self.ast.path(node);
            //     assert!(path.is_single() && !path.has_ty_args());
            //     let ptr = *ctx.vars.last().unwrap().get(&path.items[0].ident.value).unwrap();
            //     unsafe {
            //         LLVMBuildLoad(self.builder, ptr, cstring(&path.items[0].ident.value).as_ptr()).into()
            //     }
            //
            //     // let fn_path = expr.as_path().expect("unimplemented");
            //     //                 if !fn_path.is_single() || fn_path.has_ty_args() {
            //     //                     unimplemented!();
            //     //                 }
            //     //                 match fn_path.items[0].ident.value.as_str() {
            //     //                     name => {
            //     //                         match fn_call.kind {
            //     //                             FnCallKind::Free => {
            //     //                                 unsafe {
            //     //                                     LLVMGetNamedFunction(self.module, cstring(name).as_ptr() as *const _)
            //     //                                 }
            //     //                             }
            //     //                             FnCallKind::Method => {
            //     //                                 if name == "as_ptr" {
            //     //                                     assert_eq!(args.len(), 1);
            //     //                                     return unsafe {
            //     //                                         LLVMBuildGEP(self.builder, args[0], [
            //     //                                             LLVMConstInt(LLVMInt64TypeInContext(self.context), 0, 0),
            //     //                                             LLVMConstInt(LLVMInt64TypeInContext(self.context), 0, 0)].as_mut_ptr(),
            //     //                                             2, cstring("tmp").as_ptr())
            //     //                                     }.into();
            //     //                                 } else {
            //     //                                     unimplemented!()
            //     //                                 }
            //     //                             }
            //     //                         }
            //     //                     }
            //     //                 }
            // }
            NodeKind::Block =>  {
                self.block(node, ctx)
            }
            NodeKind::FnDecl => unimplemented!(),
            NodeKind::ModuleDecl => unimplemented!(),
            NodeKind::FieldAccess => unimplemented!(),
            NodeKind::StructDecl => unimplemented!(),
            NodeKind::TyExpr => unreachable!(),
        }
    }

    fn ty(&self, ty: NodeId) -> LLVMTypeRef {
        let ty = self.ast.ty_expr(ty);
        match &ty.data.value {
            &TyData::Ptr(ty) => unsafe { LLVMPointerType(self.ty(ty), 0) },
            &TyData::SymPath(path) => {
                let path = self.ast.sym_path(path);
                if !path.anchor.is_none() {
                    unimplemented!();
                }
                if path.items.len() != 1 {
                    unimplemented!();
                }
                let r = match path.items[0].ident.value.as_str() {
                    "i32" => unsafe { LLVMInt32TypeInContext(self.context) },
                    "u8" => unsafe { LLVMInt8TypeInContext(self.context) },
                    _ => unimplemented!(),
                };
                assert!(!r.is_null());
                r
            }
            _ => unimplemented!(),
        }

    }

    fn ty_void(&self) -> LLVMTypeRef {
        let r = unsafe { LLVMVoidTypeInContext(self.context) };
        assert!(!r.is_null());
        r
    }

    fn block(&self, block: NodeId, ctx: &mut ExprCtx) -> Value {
        let block = self.ast.block(block);
        ctx.vars.push(HashMap::new());
        let mut val = Value::Void;
        for expr in &block.exprs {
            val = self.expr(expr.value, ctx);
        }
        ctx.vars.pop().unwrap();
        val
    }

    fn isize_len_bytes(&self) -> u32 {
        unsafe {
            LLVMABISizeOfType(self.data_layout, LLVMIntPtrTypeInContext(self.context, self.data_layout)) as u32
        }
    }
}

impl Drop for Codegen<'_> {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeBuilder(self.builder);
            LLVMContextDispose(self.context);
            LLVMDisposeTargetMachine(self.target_machine);
        }
    }
}

struct ExprCtx<'a> {
    func: LLVMValueRef,
    fn_decl: &'a FnDecl,
    vars: Vec<HashMap<Ident, LLVMValueRef>>,
}

fn cstring(s: &str) -> CString {
    CString::new(s.as_bytes().to_vec()).unwrap()
}

fn empty_cstr() -> *const i8 {
    "\0".as_ptr() as *const _
}

#[cfg(unix)]
pub fn path_to_c_string(p: &std::path::Path) -> CString {
    use std::ffi::OsStr;
    use std::os::unix::ffi::OsStrExt;
    let p: &OsStr = p.as_ref();
    CString::new(p.as_bytes()).unwrap()
}

#[cfg(windows)]
pub fn path_to_c_string(p: &PathExpr) -> CString {
    CString::new(p.to_str().unwrap()).unwrap()
}