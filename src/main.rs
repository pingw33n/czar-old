#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::package::{Packages, PackageKind, PackageId};

mod codegen;
mod compile;
mod diag;
mod hir;
mod package;
mod semantic;
mod syntax;
#[cfg(test)]
mod test;
mod util;

fn main() {
    let packages = &mut Packages::default();

    let std = compile::compile(
        PackageId::std(),
        "misc/std.cz",
        "std".into(),
        PackageKind::Lib,
        packages,
    ).unwrap();
    packages.insert(std.into());

    let test_pkg = compile::compile(
        PackageId::new(),
        "misc/test.cz",
        "test".into(),
        PackageKind::Exe,
        packages,
    ).unwrap();
    let test_pkg_id = test_pkg.id;
    packages.insert(test_pkg.into());

    let mut cg = codegen::Codegen::new(packages);
    {
        measure_time::print_time!("llvm ir");
        cg.run(test_pkg_id);
    }
    cg.dump();
    {
        measure_time::print_time!("llvm codegen");
        cg.write("/tmp/out.o", codegen::OutputFileKind::Object);
        cg.write("/tmp/out.asm", codegen::OutputFileKind::Assembly);
    }
}
