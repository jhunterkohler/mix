//! Code formatting.
use std::{fmt::Write, sync::LazyLock};

use regex::{Captures, Regex};

/// A type storing prepared data to improve code formatting speed.
///
/// A static instance of [CodeFormatter] is used by the global [format_code].
/// Aquiring this global instance, however, requires thread safety which a
/// single local instance would not.
pub struct CodeFormatter {
    line_regex: Regex,
}

impl CodeFormatter {
    /// Create a new formatter.
    pub fn new() -> CodeFormatter {
        let line_regex =
            Regex::new(r"^(?<loc>\S+)?\s+(?<op>\S+)\s*(?<after_op>.*?)\s*$")
                .unwrap();

        Self { line_regex }
    }

    /// Format MIX assembly.
    pub fn format_code(&self, src: &str, dest: &mut String) {
        dest.reserve(src.len().saturating_sub(dest.len()));

        for line in src.lines() {
            if line.starts_with('*') {
                *dest += line;
            } else if let Some(captures) = self.line_regex.captures(line) {
                unsafe { self.format_captures(&captures, dest) };
            }

            dest.push('\n');
        }
    }

    unsafe fn format_captures(&self, captures: &Captures, dest: &mut String) {
        let loc = captures.name("loc").map_or("", |m| m.as_str());
        let op = captures.name("op").map(|m| m.as_str()).unwrap_unchecked();
        let after_op =
            captures.name("after_op").map(|m| m.as_str()).unwrap_unchecked();

        write!(dest, "{loc:10} {op:4} {after_op}").unwrap_unchecked()
    }
}

/// Format MIX assembly.
///
/// The formatted `src` is appended to `dest`.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::fmt::format_code;
///
/// let mut dest = "* comment line\n".to_string();
///
/// format_code("L EQU 500    comment", &mut dest);
/// assert_eq!(&dest, "* comment line\nL          EQU  500    comment\n");
/// ```
pub fn format_code(src: &str, dest: &mut String) {
    const CODE_FORMATTER: LazyLock<CodeFormatter> =
        LazyLock::new(|| CodeFormatter::new());

    CODE_FORMATTER.format_code(src, dest)
}

/// Format MIX assembly into a new string.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::fmt::format_code_to_string;
///
/// assert_eq!(
///     format_code_to_string("L EQU 500    comment"),
///     "L          EQU  500    comment\n"
/// );
/// ```
pub fn format_code_to_string(src: &str) -> String {
    let mut dest = String::new();
    format_code(src, &mut dest);
    return dest;
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn format_code_follows_style() {
        const UNFORMATTED: &str = concat!(
            "*     Comment line.\n",
            "L EQU   500           Comment. \n",
            "TAG ORIG 3000\n",
            "*     Another comment line.\n",
            " ORIG    3000 Comment.\n",
            "2H     INC1  3 Another comment."
        );

        const FORMATTED: &str = concat!(
            "*     Comment line.\n",
            "L          EQU  500           Comment.\n",
            "TAG        ORIG 3000\n",
            "*     Another comment line.\n",
            "           ORIG 3000 Comment.\n",
            "2H         INC1 3 Another comment.\n"
        );

        assert_eq!(format_code_to_string(UNFORMATTED), FORMATTED);
    }
}
