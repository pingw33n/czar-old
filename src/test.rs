use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::tempdir;

use crate::{compile, codegen};
use crate::hir::source_file_name;
use crate::package::{PackageKind, PackageId, Packages};
use threadpool::ThreadPool;

#[test]
fn end_to_end() {
    let root = env!("CARGO_MANIFEST_DIR");
    let path: PathBuf = [root, "test_data", "end_to_end"].iter().collect();

    let packages = &mut Packages::default();

    let std_path: PathBuf = [root, "misc", source_file_name("std").to_str().unwrap()].iter().collect();
    let std = compile::compile(
        PackageId::std(),
        std_path,
        "std".into(),
        PackageKind::Lib,
        packages,
    ).unwrap();
    packages.insert(std.into());

    let glue_obj_path = tempfile::Builder::new()
        .suffix(".o")
        .tempfile()
        .unwrap();
    exec(Command::new("cc")
        .arg([root, "misc", "glue.c"].iter().collect::<PathBuf>().to_str().unwrap())
        .arg("-c")
        .arg("-o")
        .arg(glue_obj_path.path().to_str().unwrap()));

    let tp = ThreadPool::new(num_cpus::get());

    for e in fs::read_dir(&path).unwrap() {
        let e = e.unwrap();
        if !e.path().is_dir() {
            continue;
        }
        let glue_obj_path = glue_obj_path.path().to_path_buf();
        let packages = packages.clone();
        tp.execute(move || run(&e.path(), &glue_obj_path, packages.clone()))
    }

    tp.join();
    assert_eq!(tp.panic_count(), 0);
}

fn run(path: &Path, glue_obj_path: &Path, mut packages: Packages) {
    let packages = &mut packages;
    let main: PathBuf = [path, &source_file_name("main")].iter().collect();
    let pkg = compile::compile(
        PackageId::new(),
        main,
        path.file_name().unwrap().to_str().unwrap().into(),
        PackageKind::Exe,
        packages,
    ).unwrap();
    let pkg_id = pkg.id;
    packages.insert(pkg.into());

    let mut cg = codegen::Codegen::new(packages);
    {
        measure_time::print_time!("llvm ir");
        cg.run(pkg_id);
    }

    cg.dump();

    let tmp_dir = tempdir().unwrap();

    let obj_path = tmp_dir.path().join("main.o");
    {
        measure_time::print_time!("llvm codegen");

        cg.write(&obj_path, codegen::OutputFileKind::Object);
    }

    let run_stdout_txt = path.join("run.stdout.txt");

    if run_stdout_txt.exists() {
        let exe_path = tmp_dir.path().join("exe");
        {
            measure_time::print_time!("link time");
            exec(Command::new("cc")
                .arg(obj_path.to_str().unwrap())
                .arg(glue_obj_path.to_str().unwrap())
                .arg("-o")
                .arg(exe_path.to_str().unwrap()));
        }

        let out = Command::new(exe_path.to_str().unwrap())
            .output()
            .unwrap();

        let stdout_exp = fs::read_to_string(run_stdout_txt).unwrap();
        let stdout_act = std::str::from_utf8(&out.stdout).unwrap();
        assert_eq!(stdout_act, stdout_exp);
    }
}

fn exec(cmd: &mut Command) {
    assert!(cmd
        .spawn()
        .unwrap()
        .wait()
        .unwrap()
        .success());
}