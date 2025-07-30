//! MIX code formatting.
use std::iter::repeat_n;

/// Finds offset of first whitespace character at an index greater than or
/// equal to `start`, or returns `s.len()` if no such character exists.
///
/// # Safety
///
/// * `start` must be on a valid byte boundary.
/// * `start` must be <= s.len()
unsafe fn find_ws(s: &str, start: usize) -> usize {
    // SAFETY: `start..` is valid index by function preconditions.
    unsafe { s.get_unchecked(start..) }
        .find(char::is_whitespace)
        .map(|index| index + start)
        .unwrap_or(s.len())
}

/// Finds offset of first whitespace character at an index greater than or
/// equal to `start`, or returns `s.len()` if no such character exists.
///
/// # Safety
///
/// * `start` must be on a valid byte boundary.
/// * `start` must be <= s.len()
unsafe fn find_non_ws(s: &str, start: usize) -> usize {
    // SAFETY: `start..` is valid index by function preconditions.
    unsafe { s.get_unchecked(start..) }
        .find(|c: char| !c.is_whitespace())
        .map(|index| index + start)
        .unwrap_or(s.len())
}

/// Get parts of line to format: the loc, op, and address/comment portions.
fn line_parts(line: &str) -> (&str, &str, &str) {
    // SAFETY: Each call to `find_ws` and `find_non_ws` upholds character
    // boundary preconditions for valid string indexes and slices into `line`.
    unsafe {
        let loc_end = find_ws(line, 0);
        let op_start = find_non_ws(line, loc_end);
        let op_end = find_ws(line, op_start);
        let after_op_start = find_non_ws(line, op_end);

        (
            line.get_unchecked(..loc_end),
            line.get_unchecked(op_start..op_end),
            line.get_unchecked(after_op_start..),
        )
    }
}

/// Format line containing code that is nonempty and end-trimmed.
fn format_line(line: &str, dest: &mut String) {
    debug_assert!(line.trim_end() == line);
    debug_assert!(!line.is_empty());

    let (loc, op, after_op) = line_parts(line);

    dest.push_str(loc);

    // If `op` is empty, then `after_op` must also be, and we are done.
    if op.is_empty() {
        return;
    }

    // Pad `loc` to 10 characters with spaces and add one separation space.
    if loc.len() < 10 {
        dest.extend(repeat_n(' ', 11 - loc.len()));
    } else {
        dest.push(' ');
    }

    dest.push_str(op);

    // We are done if nothing after `op`.
    if after_op.is_empty() {
        return;
    }

    // Pad `op` to 4 characters with spaces and add one separation space.
    if op.len() < 4 {
        dest.extend(repeat_n(' ', 5 - op.len()));
    } else {
        dest.push(' ');
    }

    dest.push_str(after_op);
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
/// let mut dest = "* COMMENT LINE\n".to_string();
/// format_code("L EQU 500    comment\n\n", &mut dest);
///
/// assert_eq!(&dest, "* COMMENT LINE\nL          EQU  500    comment\n");
/// ```
pub fn format_code(src: &str, dest: &mut String) {
    let src = src.trim();
    let mut last_empty = false;

    for line in src.lines().map(str::trim_end) {
        if line.is_empty() {
            if !last_empty {
                dest.push('\n');
                last_empty = true;
            }
        } else if line.starts_with('*') {
            dest.push_str(line);
            dest.push('\n');
            last_empty = false;
        } else {
            format_line(line, dest);
            dest.push('\n');
            last_empty = false;
        }
    }
}

pub fn format_code_to_string(src: &str) -> String {
    let mut dest = String::new();
    format_code(src, &mut dest);
    dest
}

#[cfg(test)]
mod tests {
    use super::*;

    const UNFORMATTED: &str = concat!(
        "\n\n",
        "* COMMENT LINE  \n",
        "A  \n",
        "A EQU  \n",
        "ABCDEFGHJK    EQU  \n",
        "ABCDEFGHJKL    EQU  \n",
        "ABCDEFGHJKL    EQU    AFTER  \n",
        "ABCDEFGHJKL    ORIG    AFTER \n",
        "ABCDEFGHJKL    ABCDE    AFTER  \n",
        "\n\n",
        "* COMMENT LINE\n",
        "\n\n",
    );

    const FORMATTED: &str = concat!(
        "* COMMENT LINE\n",
        "A\n",
        "A          EQU\n",
        "ABCDEFGHJK EQU\n",
        "ABCDEFGHJKL EQU\n",
        "ABCDEFGHJKL EQU  AFTER\n",
        "ABCDEFGHJKL ORIG AFTER\n",
        "ABCDEFGHJKL ABCDE AFTER\n",
        "\n",
        "* COMMENT LINE\n",
    );

    #[test]
    fn format_code_follows_style() {
        assert_eq!(format_code_to_string(UNFORMATTED), FORMATTED);
    }
}
