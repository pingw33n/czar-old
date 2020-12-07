use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IntrinsicKind {
    Trap,
}

impl IntrinsicKind {
    pub fn cname(self) -> &'static CStr {
        use IntrinsicKind::*;
        unsafe { CStr::from_bytes_with_nul_unchecked(match self {
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