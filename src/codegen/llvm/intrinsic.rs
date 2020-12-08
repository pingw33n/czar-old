use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntrinsicKind {
    Memcpy32,
    Memcpy64,
    Trap,
}

impl IntrinsicKind {
    pub fn cname(self) -> &'static CStr {
        use IntrinsicKind::*;
        unsafe { CStr::from_bytes_with_nul_unchecked(match self {
            Memcpy32 => b"llvm.memcpy.p0i8.p0i8.i32\0",
            Memcpy64 => b"llvm.memcpy.p0i8.p0i8.i64\0",
            Trap => b"llvm.trap\0",
        })}
    }
}

pub trait Intrinsic {
    const KIND: IntrinsicKind;

    fn func_type(llvm: &Llvm) -> TypeRef;

    fn new(func: ValueRef) -> Self;
}

pub struct Trap(ValueRef);

impl Intrinsic for Trap {
    const KIND: IntrinsicKind = IntrinsicKind::Trap;

    fn func_type(llvm: &Llvm) -> TypeRef {
        TypeRef::function(llvm.void_type(), &mut [])
    }

    fn new(func: ValueRef) -> Self {
        Self(func)
    }
}

impl Trap {
    pub fn call(&self, b: BuilderRef) -> ValueRef {
        b.call(self.0, &mut [])
    }
}

pub struct Memcpy32(ValueRef);

impl Intrinsic for Memcpy32 {
    const KIND: IntrinsicKind = IntrinsicKind::Memcpy32;

    fn func_type(llvm: &Llvm) -> TypeRef {
        let i8ptr = llvm.int_type(8).pointer();
        TypeRef::function(llvm.void_type(), &mut [i8ptr, i8ptr, llvm.int_type(32), llvm.int_type(1)])
    }

    fn new(func: ValueRef) -> Self {
        Self(func)
    }
}

impl Memcpy32 {
    pub fn call(&self, b: BuilderRef, dst: ValueRef, src: ValueRef, len: ValueRef, volatile: ValueRef) {
        b.call(self.0, &mut [dst, src, len, volatile]);
    }
}

pub struct Memcpy64(ValueRef);

impl Intrinsic for Memcpy64 {
    const KIND: IntrinsicKind = IntrinsicKind::Memcpy64;

    fn func_type(llvm: &Llvm) -> TypeRef {
        let i8ptr = llvm.int_type(8).pointer();
        TypeRef::function(llvm.void_type(), &mut [i8ptr, i8ptr, llvm.int_type(64), llvm.int_type(1)])
    }

    fn new(func: ValueRef) -> Self {
        Self(func)
    }
}

impl Memcpy64 {
    pub fn call(&self, b: BuilderRef, dst: ValueRef, src: ValueRef, len: ValueRef, volatile: ValueRef) {
        b.call(self.0, &mut [dst, src, len, volatile]);
    }
}