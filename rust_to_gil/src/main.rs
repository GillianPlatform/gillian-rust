#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;

use std::process::Command;

use lib_rtg::{config::GillianArgs, *};
use rustc_driver::RunCompiler;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

fn main() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());

    std::env::set_var("RUST_BACKTRACE", "1");
    // TODO: Custom ICE hook
    rustc_driver::install_ice_hook("https://github.com/GillianPlatform/rust-to-gil", |_| ());

    rustc_driver::init_rustc_env_logger(&handler);

    let mut args: Vec<_> = std::env::args().collect();

    let is_wrapper = args.get(1).map(|s| s.contains("rustc")).unwrap_or(false);

    if is_wrapper {
        args.remove(1);
    }

    let sysroot = sysroot_path();
    args.push(format!("--sysroot={}", sysroot));

    let normal_rustc = args
        .iter()
        .any(|arg| arg.starts_with("--print") || arg.starts_with("-vV"));
    let primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

    let has_contracts = args
        .iter()
        .any(|arg| arg == "gilogic" || arg.contains("gilogic="));

    // Did the user ask to compile this crate? Either they explicitly invoked `creusot-rustc` or this is a primary package.

    if normal_rustc || !(has_contracts) {
        eprintln!("DOING NORMAL RUST STUFF ");
        return RunCompiler::new(&args, &mut DefaultCallbacks {})
            .run()
            .unwrap();
    } else {
        let in_ui_test = std::env::var("IN_UI_TEST").is_ok();
        let gillian_args: GillianArgs = if true {
            serde_json::from_str(&std::env::var("GILLIAN_ARGS").unwrap()).unwrap_or_else(|err| {
                panic!("{err} args: {}", std::env::var("GILLIAN_ARGS").unwrap())
            })
        } else {
            eprintln!("Doing it for real");
            // panic!("NOT NORMALRUSTC {is_wrapper:?} {:?}", std::env::args());
            use lib_rtg::config::Parser;
            let all_args = crate::config::Args::parse_from(&args);
            args = all_args.rust_flags;
            args.insert(0, "rust_to_gil".to_owned());
            all_args.gillian
        };

        args.push("-Cpanic=abort".to_owned());
        args.push("-Zmir-opt-level=0".to_owned());
        // args.push("--crate-type=lib".to_owned());
        args.extend(["--cfg", "gillian"].iter().map(|x| (*x).to_owned()));

        // eprintln!("final fainl {args:?}");
        utils::init();
        let mut to_gil = callbacks::ToGil::new(gillian_args.into_config());

        match rustc_driver::RunCompiler::new(&args, &mut to_gil).run() {
            Ok(_) => log::debug!("Correct!"),
            Err(_) => log::debug!("Incorrect!"),
        }
    }
}

fn sysroot_path() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain.toml")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}
