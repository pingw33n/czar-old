use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Intrinsic {
    GcDebugMalloc,
    Memcpy32,
    Memcpy64,
}

impl Intrinsic {
    pub fn cname(self) -> &'static CStr {
        use Intrinsic::*;
        unsafe { CStr::from_bytes_with_nul_unchecked(match self {
            GcDebugMalloc => b"GC_debug_malloc\0",
            Memcpy32 => b"llvm.memcpy.p0i8.p0i8.i32\0",
            Memcpy64 => b"llvm.memcpy.p0i8.p0i8.i64\0",
        })}
    }

    pub fn type_(self, llvm: &Llvm) -> TypeRef {
        use Intrinsic::*;
        match self {
            GcDebugMalloc => {
                // TODO add `noalias` attr on return parameter
                TypeRef::function(llvm.pointer_type(llvm.int_type(8)), &mut [
                    llvm.size_type(),
                    llvm.pointer_type(llvm.int_type(8)),
                    llvm.int_type(32),
                ])
            }
            Memcpy32 => {
                let i8ptr = llvm.int_type(8).pointer();
                TypeRef::function(llvm.void_type(), &mut [i8ptr, i8ptr, llvm.int_type(32), llvm.int_type(1)])
            }
            Memcpy64 => {
                let i8ptr = llvm.int_type(8).pointer();
                TypeRef::function(llvm.void_type(), &mut [i8ptr, i8ptr, llvm.int_type(64), llvm.int_type(1)])
            }
        }
    }
}

pub fn gc_debug_malloc(llvm: &Llvm, b: BuilderRef, size: ValueRef, file: &str, line: u32) -> ValueRef {
    let file = llvm.add_global_cstring_const(file);
    let line = llvm.int_type(32).const_int(line as u128);
    b.call(llvm.intrinsic(Intrinsic::GcDebugMalloc), &mut [size, file, line])
}

pub fn memcpy(llvm: &Llvm, b: BuilderRef, dst: ValueRef, src: ValueRef, len: ValueRef, volatile: ValueRef) {
    let kind = match llvm.pointer_size_bits() {
        32 => Intrinsic::Memcpy32,
        64 => Intrinsic::Memcpy64,
        _ => panic!("invalid len type"),
    };
    b.call(llvm.intrinsic(kind), &mut [dst, src, len, volatile]);
}
