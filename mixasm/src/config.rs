use annotate_snippets::Renderer;
use anyhow::Context;
use clap::ColorChoice;
use pathdiff::diff_paths;

use std::env;
use std::fs;
use std::io::IsTerminal;
use std::io::stdout;
use std::path::Path;
use std::path::PathBuf;

use crate::cli::Cli;
use crate::error_reporter::ErrorReporter;

pub struct Config {
    pub source: String,
    pub source_path_abs: PathBuf,
    pub source_path_str: String,
    pub output_path: PathBuf,
    pub renderer: Renderer,
    pub emit_debug_info: bool,
    pub summary: bool,
}

impl Config {
    pub fn try_new(cli: &Cli) -> anyhow::Result<Self> {
        let base_path_abs = get_cwd()?;
        let source = read_source_file(&cli.file)?;
        let source_path_abs = get_full_source_path(&cli.file)?;
        let source_path_rel =
            diff_paths(&source_path_abs, &base_path_abs).unwrap();
        let source_path_str = source_path_rel.to_string_lossy().into_owned();
        let output_path = cli
            .output
            .clone()
            .unwrap_or_else(|| source_path_rel.with_extension("mix"));
        let emit_debug_info = !cli.no_debug;
        let renderer = match cli.colors {
            ColorChoice::Auto => {
                if stdout().is_terminal() {
                    Renderer::styled()
                } else {
                    Renderer::plain()
                }
            }
            ColorChoice::Always => Renderer::styled(),
            ColorChoice::Never => Renderer::plain(),
        };

        Ok(Self {
            source,
            source_path_abs,
            source_path_str,
            output_path,
            emit_debug_info,
            renderer,
            summary: cli.summary,
        })
    }

    pub fn make_error_reporter(&self) -> ErrorReporter {
        ErrorReporter::new(&self.source, &self.source_path_str, &self.renderer)
    }
}

fn get_cwd() -> anyhow::Result<PathBuf> {
    env::current_dir()
        .and_then(|cwd| cwd.canonicalize())
        .with_context(|| "Failed to get current working directory.")
}

fn read_source_file<P: AsRef<Path>>(path: P) -> anyhow::Result<String> {
    let path = path.as_ref();
    fs::read_to_string(path).with_context(|| {
        format!("Failed to read source file '{}'.", path.display())
    })
}

fn get_full_source_path<P: AsRef<Path>>(path: P) -> anyhow::Result<PathBuf> {
    let path = path.as_ref();
    path.canonicalize().with_context(|| {
        format!("Failed to get full source path for '{}'.", path.display())
    })
}
