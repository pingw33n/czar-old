use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};

#[test]
fn test() {
    let data: &[(&str, &str, Option<&str>)] = include!("test/__autogen__input.rs");

    for &(name, inp, exp) in data {
        eprintln!("test: {}", name);
        let ast = crate::syn::parse_str(inp).unwrap();
        assert_eq!(ast.display().to_string(), exp.unwrap_or(inp), "{}", name);

        if let Some(exp) = exp {
            let ast = crate::syn::parse_str(exp).unwrap();
            assert_eq!(ast.display().to_string(), exp, "unparsable disable output: {}", name);
        }
    }
}

#[test]
fn mod_file_resolution() {
    let mut files = HashMap::new();
    files.insert(Path::new("foo/bar/main.cz").to_path_buf(), r#"
        mod mod1;
        mod mod3 {}
    "#.to_string());
    files.insert(Path::new("foo/bar/mod1.cz").to_path_buf(), r#"
        pub mod mod2;
    "#.to_string());
    files.insert(Path::new("foo/bar/mod1/mod2.cz").to_path_buf(), "".to_string());
    struct Fs(HashMap<PathBuf, String>);
    impl crate::syn::Fs for Fs {
        fn read_file(&mut self, path: &Path) -> io::Result<String> {
            self.0.get(path).cloned()
                .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, "not found"))
        }
    }
    let ast = crate::syn::parse_file_with("foo/bar/main.cz", &mut Fs(files)).unwrap();
    assert_eq!(ast.sources.len(), 3);

    let root_mod = ast.module_decl(ast.root);
    let src = ast.source(root_mod.source_id.unwrap());
    assert_eq!(src.mod_name, None);
    assert_eq!(&src.path, &Path::new("foo/bar/main.cz"));

    let mod1 = ast.module_decl(root_mod.items[0]);
    let src = ast.source(mod1.source_id.unwrap());
    assert_eq!(src.mod_name, Some("mod1".into()));
    assert_eq!(&src.path, &Path::new("foo/bar/mod1.cz"));

    let mod2 = ast.module_decl(mod1.items[0]);
    let src = ast.source(mod2.source_id.unwrap());
    assert_eq!(src.mod_name, Some("mod2".into()));
    assert_eq!(&src.path, &Path::new("foo/bar/mod1/mod2.cz"));

    let mod3 = ast.module_decl(root_mod.items[1]);
    assert_eq!(mod3.source_id, None);
}