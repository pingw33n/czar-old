use std::cell::RefCell;
use std::path::Path;
use std::rc::Rc;

use crate::diag::Diag;
use crate::hir::Ident;
use crate::package::*;
use crate::semantic::check::Check;
use crate::semantic::discover::DiscoverData;
use crate::semantic::resolve::ResolveData;
use crate::syntax;
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
    id: PackageId,
    path: impl AsRef<Path>,
    name: Ident,
    kind: PackageKind,
    packages: &Packages,
) -> Result<Package, Error> {
    let mut diag = Diag::default();

    let path = path.as_ref();
    let hir = match syntax::parse::parse_file(path, &mut diag) {
        Ok(v) => v,
        Err(e) => match e.kind {
            ErrorKind::Io(io_err) => {
                let mut s = String::new();
                diag.print(path.parent().unwrap(), &mut s, &e.sources).unwrap();
                use std::fmt::Write;
                if !s.is_empty() {
                    writeln!(&mut s).unwrap();
                }
                writeln!(&mut s, "{}", io_err).unwrap();
                return Err(Error(s));
            },
            ErrorKind::Lex | ErrorKind::Parse => {
                let mut s = String::new();
                diag.print(path.parent().unwrap(), &mut s, &e.sources).unwrap();
                return Err(Error(s));
            },
        }
    };

    let discover_data = DiscoverData::build(&hir);
    // discover_data.print_scopes(&hir);

    let resolve_data = ResolveData::build(
        &discover_data,
        &hir,
        id,
        kind,
        packages,
    );

    let diag = Rc::new(RefCell::new(diag));
    let check_data = Check {
        package_id: id,
        hir: &hir,
        discover_data: &discover_data,
        resolve_data: &resolve_data,
        packages,
        diag: diag.clone(),
    }.run();
    let check_data = match check_data {
        Ok(v) => v,
        Err(_) => {
            let mut s = String::new();
            let diag = diag.borrow();
            diag.print(path.parent().unwrap(), &mut s, hir.sources()).unwrap();
            return Err(Error(s));
        }
    };

    if !diag.borrow().reports().iter().all(|r| matches!(r.severity, crate::diag::Severity::Error)) {
        todo!();
    }

    Ok(Package {
        id,
        name,
        hir,
        discover_data,
        resolve_data,
        check_data,
    })
}