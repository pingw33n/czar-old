use std::path::Path;

use crate::hir::Ident;
use crate::package::*;
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;
use crate::semantic::type_check::TypeCheck;
use crate::syntax;
use crate::diag::Diag;
use crate::syntax::parse::ErrorKind;

pub struct Error(String);

impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

pub fn compile(
    path: impl AsRef<Path>,
    name: Ident,
    kind: PackageKind,
    packages: &mut Packages,
) -> Result<PackageId, Error> {
    let diag = &mut Diag::default();

    let hir = match syntax::parse::parse_file(path, diag) {
        Ok(v) => v,
        Err(e) => match e.kind {
            ErrorKind::Io(io_err) => {
                let mut s = String::new();
                diag.print(&mut s, &e.sources).unwrap();
                use std::fmt::Write;
                if !s.is_empty() {
                    writeln!(&mut s).unwrap();
                }
                writeln!(&mut s, "{}", io_err).unwrap();
                return Err(Error(s));
            },
            ErrorKind::Lex | ErrorKind::Parse => {
                let mut s = String::new();
                diag.print(&mut s, &e.sources).unwrap();
                return Err(Error(s));
            },
        }
    };

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
    Ok(id)
}