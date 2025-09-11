use crate::cli::{cli_components::{NargoConfig, with_workspace}, proxy_cmd::proxy_to_nargo};
use clap::{Parser, Subcommand};
use nargo_cli::errors::CliError;
use std::ffi::OsString;
pub mod cli_components;
pub mod fv_cmd;
pub mod proxy_cmd;

#[derive(Parser)]
#[command(name="verno", author, version, about = "A formal verification tool for Noir. Also acts as a transparent proxy for all other nargo commands, provided nargo is installed and in your PATH.", long_about = None)]
pub struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[clap(flatten)]
    config: NargoConfig,
}

#[derive(Subcommand)]
pub enum Commands {
    /// Formal verification commands
    FormalVerify(fv_cmd::FormalVerifyCommand),
    #[command(external_subcommand)]
    External(Vec<OsString>),
}

pub fn run_cli() -> Result<(), CliError> {
    let cli = Cli::parse();

    match cli.command {
        Commands::FormalVerify(args) => with_workspace(args, cli.config, fv_cmd::run),
        Commands::External(args) => {
            proxy_to_nargo(&args);
            Ok(())
        }
    }
}
