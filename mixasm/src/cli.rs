use clap::{ColorChoice, Parser, command};
use std::path::PathBuf;

/// Assemble MIX assembly code.
#[derive(Parser, Debug)]
#[command(version, disable_help_subcommand(true))]
pub struct Cli {
    /// File to assemble.
    #[arg()]
    pub file: PathBuf,

    /// Output file.
    #[arg(short, long)]
    pub output: Option<PathBuf>,

    /// Print a summary of the assembled program.
    #[arg(long)]
    pub summary: bool,

    /// Omit debug info.
    #[arg(long)]
    pub no_debug: bool,

    /// Output coloring.
    #[arg(long, default_value_t = ColorChoice::Auto)]
    pub colors: ColorChoice,
}
