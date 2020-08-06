#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::semantic::type_check::{Types, TypeCheck};
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;
use crate::package::{Packages, Package, PackageId};
use crate::hir::Ident;

// mod codegen;
mod hir;
mod package;
mod semantic;
mod syntax;
mod util;

fn compile_package(s: &str, name: Ident, packages: &mut Packages) -> PackageId {
    let hir = syntax::parse::parse_str(s).unwrap();
    eprintln!("{}", hir.display());

    let discover_data = DiscoverData::build(&hir);
    discover_data.print_scopes(&hir);

    let package_id = packages.next_id();

    let mut resolve_data = ResolveData::build(&discover_data, &hir, package_id, packages);

    let mut types = Types::default();
    {
        let tc = &mut TypeCheck {
            resolve_data: &mut resolve_data,
            types: &mut types,
            package_id,
            packages,
            reso_ctxs: Default::default(),
        };
        if package_id.is_std() {
            tc.build_lang_types(&discover_data, &hir);
        }
        hir.traverse(tc);
    }

    packages.insert(package_id, Package {
        name,
        hir,
        discover_data,
        resolve_data,
        types,
    });
    package_id
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
    "##, "std".into(), packages);
    assert!(std.is_std());

    let my = compile_package(r##"
        fn fib(_ v: i32) -> i32 {
            if v <= 1 {
                v
            } else {
                let a: i32 = v - 1;
                let b: i32 = v - 2;
                fib(a) + fib(b)
            }
        }

        fn main() {
            mod bar {
                fn f() -> i32 {
                    let x: i32 = 0;
                    use f as Z;
                    42
                }
            }
            print_i32(fib(10));
        }

        unsafe fn print_i32(_ v: i32);

        "##, "my".into(), packages);

    // let mut cg = codegen::Codegen::new(&ast);
    // {
    //     measure_time::print_time!("llvm ir");
    //     cg.lower();
    // }
    // cg.dump();
    // {
    //     measure_time::print_time!("llvm codegen");
    //     cg.write("/tmp/out.o", codegen::OutputFileKind::Object);
    // }
}
