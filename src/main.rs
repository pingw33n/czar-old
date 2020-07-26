#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::codegen::OutputFileKind;
use slab::Slab;
use std::collections::HashMap;
use crate::sem::Context;
use crate::syn::Ast;

mod codegen;
mod sem;
mod syn;

fn main() {
    //    let mut p = Parser::new("// line comment
//    pub fn foo<A<C, D<E>>, B>() -> Int {
//        //-(1 + 10) * 42 + my::var / path::<T>::bar::foo::<U>(4242);
//        self.field;
//        self.method(1, true, false)
//    }");

    let mut ast = syn::parse_str(r##"

    extern fn puts(fmt: *u8) -> i32;

    // fn foo(x: i32, y: i32) -> i32 {
    //     (x + y) * 2
    // }

    // fn main() -> i32 {
    //     // puts("Hello, world!\n\0".as_ptr());
    //     // let x: i32 = 1 + 2;
    //     // let x: i32 = x + 6;
    //     // x * 2
    //     // super::foo::bar::XX::<T>();
    //     // foo(123, 456)
    // }


    "##).unwrap();

    eprintln!("{}", ast.display());

    let ctx = {
        let mut std_ast = Ast::new();
        let ty = std_ast.insert_struct_type(syn::Span::new(0, 0).spanned(syn::StructType {
            fields: vec![],
        }));
        std_ast.insert_struct_decl(syn::Span::new(0, 0).spanned(syn::StructDecl {
            name: syn::Span::new(0, 0).spanned("i32".into()),
            vis: Some(syn::Span::new(0, 0).spanned(syn::Vis { restrict: None })),
            ty_args: vec![],
            ty,
        }));
        let mut packages = Slab::new();
        let std = sem::PackageId(packages.insert(sem::Package {
            name: "std".into(),
            ast: std_ast,
        }));

        let mut package_by_name = HashMap::new();
        package_by_name.insert(packages[std.0].name.clone(), std);

        Context {
            packages,
            package_by_name,
            ast: &mut ast,
        }
    };


    let mut cg = codegen::Codegen::new(&ast);
    {
        measure_time::print_time!("llvm ir");
        cg.lower();
    }
    cg.dump();
    {
        measure_time::print_time!("llvm codegen");
        cg.write("/tmp/out.asm", OutputFileKind::Assembly);
    }
}
