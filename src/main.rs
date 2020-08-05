#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::semantic::type_check::{Types, TypeCheck};
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;

// mod codegen;
mod hir;
mod semantic;
mod syntax;
mod util;

fn main() {
    let hir = &mut syntax::parse::parse_str(r##"

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
        print_i32(fib(10));
    }

    unsafe fn print_i32(_ v: i32);

    "##).unwrap();

    let _ctx = {
        {
            let mut ins = |name: &str| {
                let ty = hir.insert_struct_type(syntax::Span::new(0, 0).spanned(hir::StructType {
                    fields: vec![],
                }));
                let struct_ = hir.insert_struct(syntax::Span::new(0, 0).spanned(hir::Struct {
                    name: syntax::Span::new(0, 0).spanned(name.into()),
                    vis: Some(syntax::Span::new(0, 0).spanned(hir::Vis { restrict: None })),
                    ty_args: vec![],
                    ty,
                }));
                hir.module_mut(hir.root).items.push(struct_);
            };
            ins("__unit");
            ins("bool");
            ins("i32");
        }

        hir.root
    };

    eprintln!("{}", hir.display());

    let discover_data = &DiscoverData::build(hir);
    discover_data.print_scopes(&hir);

    let resolve_data = &ResolveData::build(discover_data, hir);

    let types = &mut Types::default();
    {
        let tc = &mut TypeCheck {
            resolve: resolve_data,
            types,
        };
        tc.build_lang_types(discover_data, hir);
        hir.traverse(tc);
    }


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
