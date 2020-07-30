use std::fs::{self, File};
use std::io::prelude::*;
use std::io::BufWriter;
use std::path::Path;

const SYN_TEST_PATH: &str = "src/syntax/parse/test";

fn generate_syn_test_input() {
    const INP_CZ: &str = "__inp.cz";
    const EXP_CZ: &str = "__exp.cz";
    let out = &mut BufWriter::new(File::create(format!("{}/__autogen__input.rs", SYN_TEST_PATH)).unwrap());
    writeln!(out, "// AUTOGENERATED by build.rs").unwrap();
    writeln!(out, "&[").unwrap();
    let mut inps: Vec<_> = fs::read_dir(format!("{}/input", SYN_TEST_PATH)).unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_file())
        .map(|p| p.components().last().unwrap().as_os_str().to_str().unwrap().to_string())
        .filter(|inp| {
            let is_inp = inp.ends_with(INP_CZ);
            assert!(is_inp || inp.ends_with(EXP_CZ));
            is_inp
        })
        .collect();
    inps.sort();
    for inp in inps {
        let name = &inp[..inp.len() - INP_CZ.len()];
        let exp = format!("{}{}", name, EXP_CZ);
        let exp_code = if Path::new(&format!("{}/input/{}", SYN_TEST_PATH, exp)).is_file() {
            format!(r#"Some(include_str!("input/{}"))"#, exp)
        } else {
            "None".into()
        };
        writeln!(out, r#"("{}", include_str!("input/{}"), {}),"#, name, inp, exp_code).unwrap();
    }
    writeln!(out, "]").unwrap();
}

pub fn main() {
    generate_syn_test_input();
    println!("cargo:rerun-if-changed={}/input", SYN_TEST_PATH);
}