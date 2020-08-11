#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::semantic::type_check::{TypeCheck, Types};
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;
use crate::package::{Packages, Package, PackageId, PackageKind};
use crate::hir::Ident;

mod codegen;
mod hir;
mod package;
mod semantic;
mod syntax;
mod util;

fn compile_package(s: &str, name: Ident, kind: PackageKind, packages: &mut Packages) -> PackageId {
    let hir = syntax::parse::parse_str(s).unwrap();
    eprintln!("{}", hir.display());

    let discover_data = DiscoverData::build(&hir);
    discover_data.print_scopes(&hir);

    let id = packages.next_id();

    let resolve_data = ResolveData::build(
        &discover_data,
        &hir,
        id,
        kind,
        packages,
    );

    let types = TypeCheck {
        package_id: id,
        hir: &hir,
        discover_data: &discover_data,
        resolve_data: &resolve_data,
        packages,
    }.run();

    packages.insert(id, Package {
        id,
        name,
        hir,
        discover_data,
        resolve_data,
        types,
    });
    id
}

fn main() {
    let packages = &mut Packages::default();

    let std = compile_package(r##"
        pub mod prelude {
            pub mod v1 {
                pub use package::i32::i32;
                pub use package::bool::bool;
            }
        }
        pub mod i32 {
            pub struct i32 {}
        }
        pub mod bool {
            pub struct bool {}
        }
        struct Unit {}
    "##, "std".into(), PackageKind::Lib, packages);
    assert!(std.is_std());

    let test_pkg = compile_package(&std::fs::read_to_string("misc/test.cz").unwrap(),
        "test".into(), PackageKind::Exe, packages);

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
