#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::package::{Packages, PackageKind};

mod codegen;
mod compiler;
mod diag;
mod hir;
mod package;
mod semantic;
mod syntax;
mod util;

fn main() {
    let packages = &mut Packages::default();

    let std = compiler::compile(
        "misc/std.cz",
        "std".into(),
        PackageKind::Lib,
        packages,
    ).unwrap();
    assert!(std.is_std());

    let test_pkg = compiler::compile(
        "misc/test.cz",
        "test".into(),
        PackageKind::Exe,
        packages,
    ).unwrap();

    let mut cg = codegen::Codegen::new(packages);
    {
        measure_time::print_time!("llvm ir");
        cg.lower(test_pkg);
    }
    cg.dump();
    {
        measure_time::print_time!("llvm codegen");
        cg.write("/tmp/out.o", codegen::OutputFileKind::Object);
        cg.write("/tmp/out.asm", codegen::OutputFileKind::Assembly);
    }
}
