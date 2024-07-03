use std::error::Error;

// use clap::Parser;
use serde::{Deserialize, Serialize};

pub use clap::Parser;

#[derive(Parser, Serialize, Deserialize, Clone, Debug)]
pub struct GillianArgs {
    #[clap(long)]
    /// Location that Creusot metadata for this crate should be emitted to.
    pub metadata_path: Option<String>,
    /// Print to stdout.
    #[clap(group = "output", long)]
    pub stdout: bool,

    #[clap(long)]
    pub prophecies: bool,

    /// Print to a file.
    #[clap(group = "output", long, env)]
    pub output_file: Option<String>,
    /// Specify locations of metadata for external crates. The format is the same as rustc's `--extern` flag.
    #[clap(long = "gillian-extern", value_parser= parse_key_val::<String, String>, required=false)]
    pub extern_paths: Vec<(String, String)>,

    #[clap(long)]
    pub dependency: bool,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub stdout: bool,

    pub prophecies: bool,

    pub output_file: Option<String>,

    pub extern_paths: Vec<(String, String)>,

    pub dependency: bool,

    pub in_cargo: bool,
}

impl GillianArgs {
    pub fn into_config(self) -> Config {
        let in_cargo = std::env::var("CARGO_GILLIAN").is_ok();
        Config {
            stdout: self.stdout,
            prophecies: self.prophecies,
            output_file: self.output_file,
            extern_paths: self.extern_paths,
            dependency: self.dependency,
            in_cargo
        }
    }
}

/// Parse a single key-value pair
fn parse_key_val<T, U>(s: &str) -> Result<(T, U), Box<dyn Error + Send + Sync + 'static>>
where
    T: std::str::FromStr,
    T::Err: Error + Send + Sync + 'static,
    U: std::str::FromStr,
    U::Err: Error + Send + Sync + 'static,
{
    let pos = s
        .find('=')
        .ok_or_else(|| format!("invalid KEY=value: no `=` found in `{}`", s))?;
    Ok((s[..pos].parse()?, s[pos + 1..].parse()?))
}

#[derive(Parser)]
pub struct Args {
    #[clap(flatten)]
    pub gillian: GillianArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}
