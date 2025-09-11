use crate::cli::run_cli;

pub mod cli;

fn main() {
    let cli_output = run_cli();

    if let Err(report) = cli_output {
        eprintln!("{report:#}");
        std::process::exit(1);
    }
}
