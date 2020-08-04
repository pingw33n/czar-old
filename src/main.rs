#![allow(dead_code)]
#![deny(non_snake_case)]
#![deny(unused_must_use)]

use crate::syntax::traverse::AstTraverser;
use crate::semantic::type_check::{Types, TypeCheck};
use crate::semantic::discover_names::{Names, discover_names};
use crate::semantic::resolve_names::{ResolvedNames, ResolveNames};

// mod codegen;
mod semantic;
mod syntax;
mod util;

fn main() {
    let ast = &mut syntax::parse::parse_str(r##"

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
        // let mut std_ast = Ast::new();

        {
            let mut ins = |name: &str| {
                let ty = ast.insert_struct_type(syntax::Span::new(0, 0).spanned(syntax::StructType {
                    fields: vec![],
                }));
                let sd = ast.insert_struct_decl(syntax::Span::new(0, 0).spanned(syntax::StructDecl {
                    name: syntax::Span::new(0, 0).spanned(name.into()),
                    vis: Some(syntax::Span::new(0, 0).spanned(syntax::Vis { restrict: None })),
                    ty_args: vec![],
                    ty,
                }));
                ast.module_decl_mut(ast.root).items.push(sd);
            };
            ins("__unit");
            ins("bool");
            ins("i32");
        }

        ast.root
        // let mut packages = Slab::new();
        // let std = sem::PackageId(packages.insert(sem::Package {
        //     name: "std".into(),
        //     ast: std_ast,
        // }));
        //
        // let mut package_by_name = HashMap::new();
        // package_by_name.insert(packages[std.0].name.clone(), std);
        //
        // Context {
        //     packages,
        //     package_by_name,
        //     ast: &mut ast,
        // }
    };

    eprintln!("{}", ast.display());

    let names = &mut Names::default();
    discover_names(names, ast);

    names.print(&ast);

    let rnames = &mut ResolvedNames::default();
    {
        let mut trv = AstTraverser {
            ast: &ast,
            visitor: &mut ResolveNames::new(names, rnames),
        };
        trv.traverse();
    }

    let types = &mut Types::default();
    {
        let tc = &mut TypeCheck {
            names: rnames,
            types,
        };
        tc.build_lang_types(names, ast);
        AstTraverser {
            ast,
            visitor: tc,
        }.traverse();
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
