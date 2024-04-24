use ui_test::*;
use std::path::PathBuf;

fn main() -> Result<()> {
	let mut program = CommandBuilder::rustc();
    program.program = PathBuf::from(env!("CARGO_BIN_EXE_rust_to_gil"));
    program.args.push("-Ldependency=../target/debug/deps/".into());
    program.args.extend(["--extern".into(), "gilogic=../target/debug/libgilogic.rlib".into()]);
    program.args.extend(["--extern".into(), "creusillian=../target/debug/libcreusillian.rlib".into()]);
    program.args.push("-Zcrate-attr=feature(register_tool)".into());
    program.args.push("-Zcrate-attr=register_tool(gillian)".into());
    program.args.push("-Zcrate-attr=feature(rustc_attrs)".into());
    program.args.push("-Zcrate-attr=allow(internal_features)".into());
    program.args.push("-Zcrate-attr=feature(stmt_expr_attributes)".into());
    program.envs.push(("GILLIAN_EXEC_MODE".into(), Some("verif".into())));
    program.envs.push(("IN_UI_TEST".into(), Some("1".into())));

    let path = PathBuf::from("../tests/pass");
    let mut config = Config {
    	program,
        output_conflict_handling: OutputConflictHandling::Error,
        ..Config::rustc(path)
    };
    run_tests(config)
}
