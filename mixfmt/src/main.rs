use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process;

use clap::{Parser, arg};
use mixlib::fmt::format_code_to_string;

#[derive(Parser, Debug)]
#[command(
    version,
    disable_help_subcommand(true),
    about = "Format MIX assembly code."
)]
struct Args {
    #[arg(
        help = "Files to format. If no files are specified, standard input is \
                read."
    )]
    files: Vec<PathBuf>,

    #[arg(long, short, help = "Write files in place.")]
    write: bool,

    #[arg(
        long,
        short,
        help = "List files that do not match formatting style."
    )]
    check: bool,
}

fn read_stdin() -> io::Result<String> {
    let mut src = String::new();

    io::stdin().read_to_string(&mut src)?;
    Ok(src)
}

fn format_stdin(args: &Args) -> io::Result<()> {
    let src = read_stdin()?;
    let dest = format_code_to_string(src.trim_end());

    if args.check {
        if src != dest {
            println!("stdin");
        }
    } else {
        print!("{dest}");
    }

    Ok(())
}

fn format_file(args: &Args, path: &Path) -> io::Result<()> {
    let src = fs::read_to_string(path)?;
    let dest = format_code_to_string(src.trim_end());

    if args.check {
        if src != dest {
            println!("{}", path.display());
        }
    } else if args.write {
        fs::write(path, dest)?;
    } else {
        print!("{dest}");
    }

    Ok(())
}

fn check_io_result(res: io::Result<()>) {
    res.unwrap_or_else(|e| {
        eprintln!("Error: {e}");
        process::exit(1);
    })
}

fn main() {
    let args = Args::parse();

    if args.write && args.check {
        eprintln!("Error: Cannot specify both flags '--check' and '--write'.");
        process::exit(1);
    } else if args.files.is_empty() {
        check_io_result(format_stdin(&args));
    } else {
        for path in &args.files {
            check_io_result(format_file(&args, &path));
        }
    }
}
