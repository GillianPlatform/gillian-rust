#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;

use lib_rtg::{config::GillianArgs, *};
use rustc_driver::RunCompiler;
use rustc_session::{config::ErrorOutputType, EarlyDiagCtxt};

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

fn main() {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());

    std::env::set_var("RUST_BACKTRACE", "1");
    // TODO: Custom ICE hook
    rustc_driver::install_ice_hook("https://github.com/anonymous/anonymous", |_| ());

    rustc_driver::init_rustc_env_logger(&handler);

    let mut args: Vec<_> = std::env::args().collect();

    let is_wrapper = args.get(1).map(|s| s.contains("rustc")).unwrap_or(false);

    if is_wrapper {
        args.remove(1);
    }
    let normal_rustc = args
        .iter()
        .any(|arg| arg.starts_with("--print") || arg.starts_with("-vV"));
    let primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

    let has_contracts = args
        .iter()
        .any(|arg| arg == "gilogic" || arg.contains("gilogic="));

    // Did the user ask to compile this crate? Either they explicitly invoked `creusot-rustc` or this is a primary package.
    let user_asked_for = !is_wrapper || primary_package;

    if normal_rustc || !(user_asked_for || has_contracts) {
        return RunCompiler::new(&args, &mut DefaultCallbacks {})
            .run()
            .unwrap();
    } else {
        let in_ui_test = std::env::var("IN_UI_TEST").is_ok();
        let gillian_args: GillianArgs = if is_wrapper || in_ui_test {
            serde_json::from_str(&std::env::var("GILLIAN_ARGS").unwrap()).unwrap_or_else(|err| {
                panic!("{err} args: {}", std::env::var("GILLIAN_ARGS").unwrap())
            })
        } else {
            // panic!("NOT NORMALRUSTC {is_wrapper:?} {:?}", std::env::args());
            use lib_rtg::config::Parser;
            let all_args = crate::config::Args::parse_from(&args);
            args = all_args.rust_flags;
            all_args.gillian
        };

        args.push("-Cpanic=abort".to_owned());
        args.push("-Zmir-opt-level=0".to_owned());
        // args.push("--crate-type=lib".to_owned());
        args.extend(["--cfg", "gillian"].iter().map(|x| (*x).to_owned()));

        utils::init();
        let mut to_gil = callbacks::ToGil::new(gillian_args.into_config());

        match rustc_driver::RunCompiler::new(&args, &mut to_gil).run() {
            Ok(_) => log::debug!("Correct!"),
            Err(_) => log::debug!("Incorrect!"),
        }
    }
}
