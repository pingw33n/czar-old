use llvm_sys::*;
use llvm_sys::analysis::*;
use llvm_sys::core::*;
use llvm_sys::target::*;
use llvm_sys::target_machine::*;
use std::ffi::{CStr, CString};
use std::ptr::{self, NonNull};
use std::sync::Once;

pub use llvm_sys::LLVMIntPredicate as IntPredicate;
use llvm_sys::analysis::LLVMVerifyModule;

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct BasicBlockRef(NonNull<LLVMBasicBlock>);

impl BasicBlockRef {
    pub fn delete(self) {
        unsafe { LLVMDeleteBasicBlock(self.0.as_ptr()) }
    }
}

impl From<NonNull<LLVMBasicBlock>> for BasicBlockRef {
    fn from(v: NonNull<LLVMBasicBlock>) -> Self {
        Self(v)
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TypeRef(NonNull<LLVMType>);

impl From<NonNull<LLVMType>> for TypeRef {
    fn from(v: NonNull<LLVMType>) -> Self {
        Self(v)
    }
}

impl std::fmt::Display for TypeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            let s = NonNull::new(LLVMPrintTypeToString(self.0.as_ptr())).unwrap();
            let cs = CStr::from_ptr(s.as_ptr()).to_str().unwrap();
            let r = write!(f, "{}", cs);
            LLVMDisposeMessage(s.as_ptr());
            r
        }
    }
}

impl std::fmt::Debug for TypeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct ValueRef(NonNull<LLVMValue>);

impl ValueRef {
    pub fn param(self, i: u32) -> ValueRef {
        NonNull::new(unsafe { LLVMGetParam(self.0.as_ptr(), i) }).unwrap().into()
    }

    pub fn append_new_bb(self, name: &str) -> BasicBlockRef {
        NonNull::new(unsafe {
            LLVMAppendBasicBlock(self.0.as_ptr(), cstring(name).as_ptr())
        }).unwrap().into()
    }

    pub fn entry_bb(self: ValueRef) -> BasicBlockRef {
        NonNull::new(unsafe { LLVMGetEntryBasicBlock(self.0.as_ptr()) }).unwrap().into()
    }
}

impl From<NonNull<LLVMValue>> for ValueRef {
    fn from(v: NonNull<LLVMValue>) -> Self {
        Self(v)
    }
}

impl std::fmt::Display for ValueRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        unsafe {
            let s = NonNull::new(LLVMPrintValueToString(self.0.as_ptr())).unwrap();
            let cs = CStr::from_ptr(s.as_ptr()).to_str().unwrap();
            let r = write!(f, "{}", cs);
            LLVMDisposeMessage(s.as_ptr());
            r
        }
    }
}

impl std::fmt::Debug for ValueRef {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        std::fmt::Display::fmt(self, f)
    }
}

#[derive(Clone, Copy, Debug)]
pub enum OutputFormat {
    Assembly,
    IR,
    Object,
}

static INIT: Once = Once::new();

pub struct Llvm {
    c: NonNull<LLVMContext>,
    m: NonNull<LLVMModule>,
    target_machine: NonNull<LLVMOpaqueTargetMachine>,
    data_layout: NonNull<LLVMOpaqueTargetData>,
    builders: Vec<BuilderRef>,
}

impl Llvm {
    pub fn new() -> Self {
        INIT.call_once(|| {
            unsafe {
                LLVM_InitializeAllTargetInfos();
                LLVM_InitializeAllTargets();
                LLVM_InitializeAllTargetMCs();
                LLVM_InitializeAllAsmParsers();
                LLVM_InitializeAllAsmPrinters();
            }
        });
        let c;
        let m;
        let target_machine;
        let data_layout;
        unsafe {
            c = NonNull::new(LLVMContextCreate()).unwrap();
            m = NonNull::new(LLVMModuleCreateWithNameInContext(
                b"codegen\0".as_ptr() as *const _, c.as_ptr())).unwrap();

            let triple = NonNull::new(LLVMGetDefaultTargetTriple()).unwrap();
            let mut target = ptr::null_mut();
            let mut error = ptr::null_mut();
            assert_eq!(LLVMGetTargetFromTriple(triple.as_ptr(), &mut target, &mut error), 0,
                "{}", CStr::from_ptr(error).to_string_lossy());
            target_machine = NonNull::new(LLVMCreateTargetMachine(
                target, triple.as_ptr(), empty_cstr(), empty_cstr(),
                LLVMCodeGenOptLevel::LLVMCodeGenLevelDefault,
                LLVMRelocMode::LLVMRelocDefault,
                LLVMCodeModel::LLVMCodeModelDefault)).unwrap();

            LLVMSetTarget(m.as_ptr(), triple.as_ptr());
            LLVMDisposeMessage(triple.as_ptr());

            data_layout = NonNull::new(LLVMCreateTargetDataLayout(target_machine.as_ptr())).unwrap();
            LLVMSetModuleDataLayout(m.as_ptr(), data_layout.as_ptr());
        }
        Self {
            c,
            m,
            target_machine,
            data_layout,
            builders: Vec::new(),
        }
    }

    pub fn new_builder(&mut self) -> BuilderRef {
        let b = BuilderRef(NonNull::new(unsafe { LLVMCreateBuilderInContext(self.c.as_ptr()) }).unwrap());
        self.builders.push(b);
        b
    }

    pub fn add_function(&self, name: &str, ty: TypeRef) -> ValueRef {
        let name = CString::new(name).unwrap();
        NonNull::new(unsafe {
            LLVMAddFunction(self.m.as_ptr(), name.as_ptr(), ty.0.as_ptr())
        }).unwrap().into()
    }

    pub fn new_basic_block(&self, name: &str) -> BasicBlockRef {
        NonNull::new(unsafe {
            LLVMCreateBasicBlockInContext(self.c.as_ptr(), cstring(name).as_ptr())
        }).unwrap().into()
    }

    pub fn const_struct(&self, fields: &mut [ValueRef]) -> ValueRef {
        NonNull::new(unsafe {
            LLVMConstStructInContext(self.c.as_ptr(), fields.as_mut_ptr() as *mut _, 0, 0)
        }).unwrap().into()
    }

    pub fn int_type(&self, bit_count: u32) -> TypeRef {
        NonNull::new(unsafe {
            LLVMIntTypeInContext(self.c.as_ptr(), bit_count)
        }).unwrap().into()
    }

    pub fn struct_type(&self, field_tys: &mut [TypeRef]) -> TypeRef {
        NonNull::new(unsafe {
            LLVMStructTypeInContext(self.c.as_ptr(),
                field_tys.as_mut_ptr() as *mut _, field_tys.len() as u32, 0)
        }).unwrap().into()
    }

    pub fn emit(&self, out: &mut impl std::io::Write, format: OutputFormat) -> std::io::Result<()> {
        match format {
            OutputFormat::IR => {
                unsafe {
                    let s = NonNull::new(LLVMPrintModuleToString(self.m.as_ptr())).unwrap();
                    let cs = CStr::from_ptr(s.as_ptr());
                    let r = out.write_all(cs.to_bytes());
                    LLVMDisposeMessage(s.as_ptr());
                    r
                }
            }
            OutputFormat::Assembly | OutputFormat::Object => {
                let ft = match format {
                    OutputFormat::Assembly => LLVMCodeGenFileType::LLVMAssemblyFile,
                    OutputFormat::Object => LLVMCodeGenFileType::LLVMObjectFile,
                    OutputFormat::IR => unreachable!(),
                };
                unsafe {
                    let r = LLVMVerifyModule(self.m.as_ptr(), LLVMVerifierFailureAction::LLVMPrintMessageAction, ptr::null_mut());
                    assert!(r == 0, "LLVMVerifyModule failed");

                    let mut error = ptr::null_mut();
                    let mut buf = ptr::null_mut();
                    let r = LLVMTargetMachineEmitToMemoryBuffer(
                        self.target_machine.as_ptr(),
                        self.m.as_ptr(),
                        ft,
                        &mut error,
                        &mut buf);
                    let r = if r == 0 {
                        let buf = NonNull::new(buf).unwrap();
                        let p = LLVMGetBufferStart(buf.as_ptr());
                        let len = LLVMGetBufferSize(buf.as_ptr());
                        out.write_all(std::slice::from_raw_parts(p as *const u8, len))
                    } else {
                        Err(std::io::Error::new(std::io::ErrorKind::InvalidInput,
                            CStr::from_ptr(error).to_string_lossy().to_owned()))
                    };
                    if !buf.is_null() {
                        LLVMDisposeMemoryBuffer(buf);
                    }
                    r
                }
            }
        }

    }
}

impl Drop for Llvm {
    fn drop(&mut self) {
        unsafe {
            for b in &self.builders {
                LLVMDisposeBuilder(b.0.as_ptr());
            }
            LLVMContextDispose(self.c.as_ptr());
            LLVMDisposeTargetMachine(self.target_machine.as_ptr());
        }
    }
}

impl std::fmt::Display for Llvm {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let buf = &mut Vec::new();
        if self.emit(buf, OutputFormat::IR).is_err() {
            return Err(std::fmt::Error);
        }
        write!(f, "{}", std::str::from_utf8(buf).unwrap())
    }
}

pub type BuilderId = usize;

#[derive(Clone, Copy)]
pub struct BuilderRef(NonNull<LLVMBuilder>);

impl BuilderRef {
    pub fn position_at_end(&self, bb: BasicBlockRef) {
        unsafe { LLVMPositionBuilderAtEnd(self.0.as_ptr(), bb.0.as_ptr()); }
    }

    pub fn alloca(&self, name: &str, ty: TypeRef) -> ValueRef {
        NonNull::new(unsafe {
            LLVMBuildAlloca(self.0.as_ptr(), ty.0.as_ptr(), cstring(name).as_ptr())
        }).unwrap().into()
    }

    pub fn load(&self, v: ValueRef) -> ValueRef {
        NonNull::new(unsafe { LLVMBuildLoad(self.0.as_ptr(), v.0.as_ptr(), empty_cstr()) }).unwrap().into()
    }

    pub fn store(&self, v: ValueRef, ptr: ValueRef) -> ValueRef {
        NonNull::new(unsafe { LLVMBuildStore(self.0.as_ptr(), v.0.as_ptr(), ptr.0.as_ptr()) }).unwrap().into()
    }

    pub fn ret(&self, v: ValueRef) -> ValueRef {
        NonNull::new(unsafe { LLVMBuildRet(self.0.as_ptr(), v.0.as_ptr()) }).unwrap().into()
    }

    pub fn call(&self, callee: ValueRef, args: &mut [ValueRef]) -> ValueRef {
        NonNull::new(unsafe {
            LLVMBuildCall(
                self.0.as_ptr(),
                callee.0.as_ptr(),
                args.as_mut_ptr() as *mut _,
                args.len() as u32,
                empty_cstr())
        }).unwrap().into()
    }

    pub fn cond_br(&self, cond: ValueRef, if_true: BasicBlockRef, if_false: BasicBlockRef) -> ValueRef {
        NonNull::new(unsafe {
            LLVMBuildCondBr(self.0.as_ptr(), cond.0.as_ptr(), if_true.0.as_ptr(), if_false.0.as_ptr())
        }).unwrap().into()
    }

    pub fn br(&self, to: BasicBlockRef) -> ValueRef {
        NonNull::new(unsafe { LLVMBuildBr(self.0.as_ptr(), to.0.as_ptr()) }).unwrap().into()
    }

    pub fn add(&self, left: ValueRef, right: ValueRef) -> ValueRef {
        NonNull::new(unsafe {
            LLVMBuildAdd(self.0.as_ptr(), left.0.as_ptr(), right.0.as_ptr(), empty_cstr())
        }).unwrap().into()
    }

    pub fn icmp(&self, left: ValueRef, right: ValueRef, predicate: IntPredicate) -> ValueRef {
        NonNull::new(unsafe {
            LLVMBuildICmp(self.0.as_ptr(), predicate, left.0.as_ptr(), right.0.as_ptr(), empty_cstr())
        }).unwrap().into()
    }

    pub fn sub(&self, left: ValueRef, right: ValueRef) -> ValueRef {
        NonNull::new(unsafe {
            LLVMBuildSub(self.0.as_ptr(), left.0.as_ptr(), right.0.as_ptr(), empty_cstr())
        }).unwrap().into()
    }
}

pub fn const_int(ty: TypeRef, v: u128) -> ValueRef {
    NonNull::new(unsafe {
        LLVMConstIntOfArbitraryPrecision(ty.0.as_ptr(), 2, [v as u64, (v >> 64) as u64].as_ptr())
    }).unwrap().into()
}

pub fn function_type(ret_ty: TypeRef, param_tys: &mut [TypeRef]) -> TypeRef {
    NonNull::new(unsafe {
        LLVMFunctionType(ret_ty.0.as_ptr(), param_tys.as_mut_ptr() as *mut _, param_tys.len() as u32, 0)
    }).unwrap().into()
}

fn cstring(s: &str) -> CString {
    CString::new(s.as_bytes().to_vec()).unwrap()
}

fn empty_cstr() -> *const i8 {
    "\0".as_ptr() as *const _
}