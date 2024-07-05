use std::path::PathBuf;
use ui_test::*;

fn main() -> Result<()> {
    let config1 = build_config(PathBuf::from("../tests/noproph"), false);
    let config2 = build_config(PathBuf::from("../tests/proph"), true);
    let config = build_config(PathBuf::from("../tests/multiple_lifetimes"), false);
    let config3 = build_config(PathBuf::from("../tests/pass"), false);
    run_tests(config1)?;
    run_tests(config)?;
    run_tests(config2)?;
    run_tests(config3)?;
    Ok(())
}

fn build_config(path: PathBuf, prophecies: bool) -> Config {
    let mut program = CommandBuilder::rustc();

    program.program = PathBuf::from(env!("CARGO_BIN_EXE_rust_to_gil"));
    // program
    //     .args
    //     .push("-Ldependency=../target/debug/deps/".into());
    // program.args.extend([
    //     "--extern".into(),
    //     "gilogic=../target/debug/libgilogic.rlib".into(),
    // ]);
    // program.args.extend([
    //     "--extern".into(),
    //     "creusillian=../target/debug/libcreusillian.rlib".into(),
    // ]);
    program
        .args
        .push("-Zcrate-attr=feature(register_tool)".into());
    program
        .args
        .push("-Zcrate-attr=register_tool(gillian)".into());
    program
        .args
        .push("-Zcrate-attr=feature(rustc_attrs)".into());
    program
        .args
        .push("-Zcrate-attr=allow(internal_features)".into());
    program
        .args
        .push("-Zcrate-attr=feature(stmt_expr_attributes)".into());
    program.envs.push(("IN_UI_TEST".into(), Some("1".into())));

    if prophecies {
        program.envs.push((
            "GILLIAN_ARGS".into(),
            Some(r#"{ "stdout": true, "prophecies": true, "dependency": false, "extern_paths": [], "output_file": null }"#.into()),
        ));
    } else {
        program.envs.push((
            "GILLIAN_ARGS".into(),
            Some(r#"{ "stdout": true, "prophecies": false, "dependency": false, "extern_paths": [], "output_file": null }"#.into()),
        ));
    }

    // program.envs.push(("RUST_LOG".into(), Some("trace".into())));

    let mut config = Config {
        program,
        output_conflict_handling: OutputConflictHandling::Error,
        ..Config::rustc(path)
    };

    let mut dep_builder = CommandBuilder::cargo();
    dep_builder.envs.push((
        "RUSTC_WRAPPER".into(),
        Some(env!("CARGO_BIN_EXE_rust_to_gil").into()),
    ));
    dep_builder.envs.push((
        "GILLIAN_ARGS".into(),
        // Some("true".into())
        Some(r#"{ "stdout": true, "prophecies": true, "dependency": true, "extern_paths": [], "output_file": null }"#.into()),
    ));
    // dep_builder.program = PathBuf::from(env!("CARGO_BIN_EXE_rust_to_gil"));

    config.dependency_builder = dep_builder;
    config.dependencies_crate_manifest_path = Some(PathBuf::from("../tests/Cargo.toml"));
    config.out_dir = PathBuf::from("../target/ui");
    config.filter(r"(\d{4})-(\d\d)-(\d\d)T(\d\d):(\d\d):(\d\d).", "TIMESTAMP");
    config
}
