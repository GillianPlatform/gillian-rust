use std::{env, process::{exit, Command}};

use clap::*;
use serde::{Deserialize, Serialize};
use std::error::Error;

#[derive(Parser, Serialize, Deserialize, Clone, Debug)]
pub struct GillianArgs {
    #[clap(long)]
    /// Location that Creusot metadata for this crate should be emitted to.
    pub metadata_path: Option<String>,
    /// Print to stdout.
    #[clap(group = "output", long)]
    pub stdout: bool,

    #[clap(long, required = true)]
    pub prophecies: bool,

    /// Print to a file.
    #[clap(group = "output", long, env)]
    pub output_file: Option<String>,
    /// Specify locations of metadata for external crates. The format is the same as rustc's `--extern` flag.
    #[clap(long = "gillian-extern", value_parser= parse_key_val::<String, String>, required=false)]
    pub extern_paths: Vec<(String, String)>,

    #[clap(group = "dependency", long)]
    pub dependency : bool,
}

/// Parse a single key-value pair
fn parse_key_val<T, U>(s: &str) -> Result<(T, U), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    let pos = s.find('=').ok_or_else(|| format!("invalid KEY=value: no `=` found in `{}`", s))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

#[derive(Parser, Debug)]
pub struct Args {
    #[clap(flatten)]
    pub gillian: GillianArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

fn main() {
    let args = Args::parse_from(std::env::args().skip(1));

    let gillian_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("rust_to_gil");

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = if std::env::var_os("GILLIAN_CONTINUE").is_some() { "build" } else { "check" };
    let toolchain = toolchain_channel()
        .expect("Expected `cargo-gillian` to be built with a valid toolchain file");
    let mut cmd = Command::new(cargo_path);
    cmd.arg(format!("+{toolchain}"))
        .arg(&cargo_cmd)
        .args(args.rust_flags)
        .env("RUSTC_WRAPPER", gillian_rustc_path)
        .env("CARGO_GILLIAN", "1");

    cmd.env("GILLIAN_ARGS", serde_json::to_string(&args.gillian).unwrap());

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}

fn toolchain_channel() -> Option<String> {
    let toolchain: toml::Value = toml::from_str(include_str!("../../rust-toolchain.toml")).ok()?;
    let channel = toolchain["toolchain"]["channel"].as_str()?;
    Some(channel.into())
}
