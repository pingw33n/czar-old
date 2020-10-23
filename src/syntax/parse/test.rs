use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};

fn parse_str(s: String) -> crate::hir::Hir {
    let diag = &mut Default::default();
    match crate::syntax::parse::parse_str(s, diag) {
        Ok(hir) => hir,
        Err(err) => {
            panic!("{}", diag.print("", &err.sources));
        }
    }
}

#[test]
fn test() {
    let data: &[(&str, &str, Option<&str>)] = include!("test/__autogen__input.rs");

    for &(name, inp, exp) in data {
        eprintln!("test: {}", name);

        let hir = parse_str(inp.into());
        assert_eq!(hir.display().to_string(), exp.unwrap_or(inp), "{}", name);

        if let Some(exp) = exp {
            let hir = parse_str(exp.into());
            assert_eq!(hir.display().to_string(), exp, "expected output doesn't parse into itself: {}", name);
        }
    }
}

#[test]
fn mod_file_resolution() {
    let mut files = HashMap::new();
    files.insert(Path::new("foo/bar/main.cz").to_path_buf(), r#"
        module mod1;
        module mod3 {}
    "#.to_string());
    files.insert(Path::new("foo/bar/mod1.cz").to_path_buf(), r#"
        pub module mod2;
    "#.to_string());
    files.insert(Path::new("foo/bar/mod1/mod2.cz").to_path_buf(), "".to_string());
    struct Fs(HashMap<PathBuf, String>);
    impl crate::syntax::parse::Fs for Fs {
        fn read_file(&mut self, path: &Path) -> io::Result<String> {
            self.0.get(path).cloned()
                .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "not found"))
        }
    }
    let hir = crate::syntax::parse::parse_file_with("foo/bar/main.cz", &mut Fs(files),
        &mut Default::default()).unwrap();
    assert_eq!(hir.sources().len(), 3);

    let root_mod = hir.module(hir.root);
    let src = &hir.sources()[root_mod.source_id.unwrap()];
    assert_eq!(src.mod_name, None);
    assert_eq!(&src.path, &Path::new("foo/bar/main.cz"));

    let mod1 = hir.module(root_mod.items[0]);
    let src = &hir.sources()[mod1.source_id.unwrap()];
    assert_eq!(src.mod_name, Some("mod1".into()));
    assert_eq!(&src.path, &Path::new("foo/bar/mod1.cz"));

    let mod2 = hir.module(mod1.items[0]);
    let src = &hir.sources()[mod2.source_id.unwrap()];
    assert_eq!(src.mod_name, Some("mod2".into()));
    assert_eq!(&src.path, &Path::new("foo/bar/mod1/mod2.cz"));

    let mod3 = hir.module(root_mod.items[1]);
    assert_eq!(mod3.source_id, None);
}