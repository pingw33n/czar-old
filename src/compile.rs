use std::path::Path;

use crate::diag::{Diag, DiagRef};
use crate::hir::Ident;
use crate::package::*;
use crate::semantic::check::Check;
use crate::semantic::diag::SemaDiag;
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
    let base_dir = path.parent().unwrap();

    let hir = match syntax::parse::parse_file(path, &mut diag) {
        Ok(v) => v,
        Err(e) => match e.kind {
            ErrorKind::Io(io_err) => {
                let mut s = diag.print(base_dir, &e.sources).to_string();
                use std::fmt::Write;
                writeln!(&mut s, "{}", io_err).unwrap();
                return Err(Error(s));
            },
            ErrorKind::Lex | ErrorKind::Parse => {
                return Err(Error(diag.print(base_dir, &e.sources).to_string()));
            },
        }
    };

    let discover_data = DiscoverData::build(&hir);
    // discover_data.print_scopes(&hir);

    let diag = SemaDiag {
        diag: DiagRef::new(diag.into()),
        error_state: Default::default(),
    };

    let resolve_data = ResolveData::build(
        &discover_data,
        &hir,
        id,
        &name,
        kind,
        packages,
        diag.clone(),
    );

    let check_data = Check {
        package_id: id,
        hir: &hir,
        discover_data: &discover_data,
        resolve_data: &resolve_data,
        packages,
        diag: diag.clone(),
    }.run();

    {
        let diag = diag.diag.borrow();
        if !diag.reports().iter().all(|r| matches!(r.severity, crate::diag::Severity::Error)) {
            todo!();
        }
        if !diag.reports().is_empty() {
            let s = diag.print(base_dir, hir.sources()).to_string();
            return Err(Error(s));
        }
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