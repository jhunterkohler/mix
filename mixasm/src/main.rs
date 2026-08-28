use anyhow::{self, Context};
use clap::Parser;
use human_panic::setup_panic;
use mixlib::asm::{Program, assemble};
use mixlib::ast::Ast;
use mixlib::bin::Encode;

use std::fs;
use std::str::FromStr;

use crate::cli::Cli;
use crate::config::Config;
use crate::summary::Summary;

mod cli;
mod config;
mod error_reporter;
mod summary;

fn could_not_finish() -> anyhow::Error {
    anyhow::anyhow!("Could not finish assembly due to above errors.")
}

fn do_parse(config: &Config) -> anyhow::Result<Ast> {
    Ast::from_str(&config.source).map_err(|errors| {
        let reporter = config.make_error_reporter();

        for err in errors {
            reporter.report_parse_error(&err);
        }

        could_not_finish()
    })
}

fn do_assemble(config: &Config, ast: &Ast) -> anyhow::Result<Program> {
    assemble(ast, &config.source, Some(config.source_path_abs.clone()), true)
        .map_err(|errors| {
            let reporter = config.make_error_reporter();

            for err in errors {
                reporter.report_assembly_error(&err);
            }

            could_not_finish()
        })
}

fn do_output(config: &Config, program: &Program) -> anyhow::Result<()> {
    let mut buf = Vec::new();
    program.encode(&mut buf).unwrap();

    fs::write(&config.output_path, buf).with_context(|| {
        format!(
            "Failed to write to output file '{}'.",
            config.output_path.display()
        )
    })
}

fn main() -> anyhow::Result<()> {
    setup_panic!();

    let cli = Cli::parse();
    let config = Config::try_new(&cli)?;
    let ast = do_parse(&config)?;
    let mut program = do_assemble(&config, &ast)?;

    if config.summary {
        println!(
            "{}",
            Summary::new(
                &config.source,
                &program,
                program.debug_info().unwrap()
            )
        );
    }

    if !config.emit_debug_info {
        program.take_debug_info();
    }

    do_output(&config, &program)?;

    Ok(())
}
