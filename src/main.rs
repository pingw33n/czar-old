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
    ).map_err(|e| { eprintln!("{}", e); std::process::exit(1); }).unwrap();
    packages.insert(std.into());

    let path = std::env::args().nth(1).unwrap();
    let test_pkg = compile::compile(
        PackageId::new(),
        path,
        "test".into(),
        PackageKind::Exe,
        packages,
    ).map_err(|e| { eprintln!("{}", e); std::process::exit(1); }).unwrap();
    let test_pkg_id = test_pkg.id;
    packages.insert(test_pkg.into());

    let mut cg = codegen::Codegen::new(packages);
    {
        measure_time::print_time!("llvm ir");
        cg.lower(test_pkg_id);
    }
    dbg!(&cg);
    {
        measure_time::print_time!("llvm codegen");
        cg.emit_to_file("/tmp/out.ll", codegen::OutputFormat::IR).unwrap();
        cg.emit_to_file("/tmp/out.o", codegen::OutputFormat::Object).unwrap();
        cg.emit_to_file("/tmp/out.asm", codegen::OutputFormat::Assembly).unwrap();
    }
}
