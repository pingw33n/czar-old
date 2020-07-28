#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::codegen::OutputFileKind;
use slab::Slab;
use std::collections::HashMap;
use crate::sem::{Context, DiscoverNames, AstTraverser, Namespace};
use crate::syn::Ast;

mod codegen;
mod sem;
mod syn;
mod util;

fn main() {
    let mut ast = syn::parse_str(r##"

    fn fib(_ v: i32) -> i32 {
        if v <= 1 {
            v
        } else {
            let a = v - 1;
            let b = v - 2;
            fib(a) + fib(b)
        }
    }

    fn fib() {}

    fn main() {
        print_i32(fib(10));
    }

    unsafe fn print_i32(_ v: i32);

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

    let mut ns = Namespace::default();
    {
        let mut trv = AstTraverser {
            ast: &ast,
            namespace: &mut ns,
            visitor: &mut DiscoverNames,
        };
        trv.traverse();
    }

    ns.print(&ast);


    // let mut cg = codegen::Codegen::new(&ast);
    // {
    //     measure_time::print_time!("llvm ir");
    //     cg.lower();
    // }
    // cg.dump();
    // {
    //     measure_time::print_time!("llvm codegen");
    //     cg.write("/tmp/out.asm", OutputFileKind::Assembly);
    // }
}
