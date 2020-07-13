#[test]
fn test() {
    let data: &[(&str, &str, Option<&str>)] = include!("test/__autogen__input.rs");

    for &(name, inp, exp) in data {
        let ast = crate::syn::parse_str(inp).unwrap();
        assert_eq!(ast.display().to_string(), exp.unwrap_or(inp), "{}", name);

        if let Some(exp) = exp {
            let ast = crate::syn::parse_str(exp).unwrap();
            assert_eq!(ast.display().to_string(), exp, "unparsable exp: {}", name);
        }
    }
}