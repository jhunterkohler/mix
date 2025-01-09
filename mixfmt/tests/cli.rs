use std::fs;
use std::io::Write;

use assert_cmd::Command;
use tempfile::NamedTempFile;

const PRIMES_FORMATTED: &str = include_str!("primes-formatted.mixal");
const PRIMES_UNFORMATTED: &str = include_str!("primes-unformatted.mixal");

fn mixfmt_cmd() -> Command {
    Command::cargo_bin("mixfmt").unwrap()
}

fn make_tmpfile(data: &str) -> NamedTempFile {
    let mut tmp = NamedTempFile::new().unwrap();

    write!(tmp, "{data}").unwrap();
    tmp.flush().unwrap();
    tmp
}

#[test]
fn print_help() {
    mixfmt_cmd().args(["-h"]).assert().success();
}

#[test]
fn format_primes_from_stdin() {
    mixfmt_cmd()
        .write_stdin(PRIMES_UNFORMATTED)
        .assert()
        .success()
        .stdout(PRIMES_FORMATTED);
}

#[test]
fn format_primes_from_file() {
    let tmp = make_tmpfile(PRIMES_UNFORMATTED);

    mixfmt_cmd()
        .args([tmp.path()])
        .assert()
        .success()
        .stdout(PRIMES_FORMATTED);
}

#[test]
fn format_primes_from_file_and_write() {
    let tmp = make_tmpfile(PRIMES_UNFORMATTED);

    mixfmt_cmd().args([tmp.path().to_str().unwrap(), "-w"]).assert().success();
    assert_eq!(fs::read_to_string(tmp.path()).unwrap(), PRIMES_FORMATTED);
}

#[test]
fn check_unformatted_primes_from_file() {
    let tmp = make_tmpfile(PRIMES_UNFORMATTED);

    mixfmt_cmd()
        .args([tmp.path().to_str().unwrap(), "-c"])
        .assert()
        .success()
        .stdout(tmp.path().to_str().unwrap().to_string() + "\n");
}

#[test]
fn check_unformatted_primes_from_stdin() {
    mixfmt_cmd()
        .args(["-c"])
        .write_stdin(PRIMES_UNFORMATTED)
        .assert()
        .success()
        .stdout("stdin\n");
}

#[test]
fn check_formatted_primes_from_file() {
    let tmp = make_tmpfile(PRIMES_FORMATTED);

    mixfmt_cmd()
        .args([tmp.path().to_str().unwrap(), "-c"])
        .assert()
        .success()
        .stdout("");
}

#[test]
fn check_formatted_primes_from_stdin() {
    mixfmt_cmd()
        .args(["-c"])
        .write_stdin(PRIMES_FORMATTED)
        .assert()
        .success()
        .stdout("");
}

#[test]
fn fail_on_check_and_write_flags() {
    mixfmt_cmd().args(["-c", "-w"]).assert().failure();
}
