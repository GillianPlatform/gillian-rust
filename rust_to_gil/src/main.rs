#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;

use std::process::Command;

use lib_rtg::*;
use rustc_session::{config::ErrorOutputType, EarlyErrorHandler};

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

fn main() {
    let handler = EarlyErrorHandler::new(ErrorOutputType::default());
    // TODO: Custom ICE hook
    rustc_driver::install_ice_hook("https://github.com/GillianPlatform/rust-to-gil", |_| ());

    rustc_driver::init_rustc_env_logger(&handler);

    let mut args: Vec<_> = std::env::args().collect();

    let opts = config::Config::of_env();

    args.push(format!("--sysroot={}", sysroot_path()));
    args.push("-Cpanic=abort".to_owned());
    args.push("-Zmir-opt-level=0".to_owned());
    args.push("--crate-type=lib".to_owned());
    args.extend(["--cfg", "gillian"].iter().map(|x| (*x).to_owned()));

    utils::init();
    let mut to_gil = callbacks::ToGil::new(opts);

    match rustc_driver::RunCompiler::new(&args, &mut to_gil).run() {
        Ok(_) => log::debug!("Correct!"),
        Err(_) => log::debug!("Incorrect!"),
    }
}
