use std::str::Chars;

use crate::source::Span;

const SPACES: [&str; 12] = [
    "",
    " ",
    "  ",
    "   ",
    "    ",
    "     ",
    "      ",
    "       ",
    "        ",
    "         ",
    "          ",
    "           ",
];

struct Formatter<'a> {
    src: &'a str,
    it: Chars<'a>,
    empties: usize,
    dest: &'a mut String,
}

impl<'a> Formatter<'a> {
    fn new(src: &'a str, dest: &'a mut String) -> Self {
        let src = src.trim();
        Self { src, it: src.chars(), empties: 0, dest }
    }

    /// Gets current position.
    fn pos(&self) -> usize {
        self.src.len() - self.it.as_str().len()
    }

    /// Get the next character of input without consuming it.
    fn peek(&self) -> Option<char> {
        self.it.clone().next()
    }

    /// Get the 2nd next character of input without consuming anything.
    fn peek2(&self) -> Option<char> {
        self.it.clone().nth(1)
    }

    /// Get the next character of input and consume it.
    fn next(&mut self) -> Option<char> {
        self.it.next()
    }

    /// Ignore the next sequence of inline whitespace characters.
    fn ignore_inline_whitespace(&mut self) {
        loop {
            match self.peek() {
                // "\r\n" style newline
                Some('\r') if self.peek2() == Some('\n') => break,
                // "\n" style newline
                Some('\n') => break,
                Some(c) if c.is_whitespace() => {
                    self.next();
                }
                _ => break,
            }
        }
    }

    /// Get the span of the next series of non-whitespace characters.
    fn get_non_whitespace(&mut self) -> Span {
        let start = self.pos();
        while self.peek().is_some_and(|c| !c.is_whitespace()) {
            self.next();
        }
        Span::new(start, self.pos())
    }

    /// Get a comment starting at the current position. Ignores other
    /// whitespace to the start of next line.
    fn get_comment_to_nextline(&mut self) -> Span {
        let start = self.pos();
        let mut end = start;

        loop {
            match self.peek() {
                None => break,
                Some('\n') => {
                    self.next();
                    break;
                }
                Some('\r') if self.peek2() == Some('\n') => {
                    self.next();
                    self.next();
                    break;
                }
                Some(c) if !c.is_whitespace() => {
                    self.next();
                    end = self.pos();
                }
                _ => {
                    self.next();
                }
            }
        }

        Span::new(start, end)
    }

    fn format(mut self) {
        if self.src.is_empty() {
            self.dest.push('\n');
        } else {
            loop {
                match self.peek() {
                    Some('*') => self.format_comment_line(),
                    Some(_) => self.format_code_line(),
                    None => break,
                }
            }
        }
    }

    fn format_comment_line(&mut self) {
        let span = self.get_comment_to_nextline();
        self.dest.push_str(&self.src[span]);
        self.dest.push('\n');
        self.empties = 0;
    }

    fn format_code_line(&mut self) {
        let loc = self.get_non_whitespace();
        self.ignore_inline_whitespace();
        let op = self.get_non_whitespace();
        self.ignore_inline_whitespace();
        let addr = self.get_non_whitespace();
        let comment = self.get_comment_to_nextline();

        if op.is_empty() {
            if loc.is_empty() {
                // Entire line is empty.
                return self.format_empty_line();
            } else {
                // There is only a LOC.
                self.dest.push_str(&self.src[loc]);
            }
        } else {
            // LOC is given 10 columns.
            let spaces = SPACES[11usize.saturating_sub(loc.len()).max(1)];
            self.dest.push_str(&self.src[loc]);
            self.dest.push_str(spaces);
            self.dest.push_str(&self.src[op]);

            if !addr.is_empty() {
                // OP is given 4 columns.
                let spaces = SPACES[5usize.saturating_sub(op.len()).max(1)];
                self.dest.push_str(spaces);
                self.dest.push_str(&self.src[addr]);

                if !comment.is_empty() {
                    self.dest.push_str(&self.src[comment]);
                }
            }
        }

        self.dest.push('\n');
        self.empties = 0;
    }

    fn format_empty_line(&mut self) {
        // Allow at most 2 empty lines in sequence.
        if self.empties < 2 {
            self.dest.push('\n');
        }
        self.empties += 1;
    }
}

pub fn format(src: &str, dest: &mut String) {
    Formatter::new(src, dest).format()
}

pub fn format_to_string(src: &str) -> String {
    let mut dest = String::new();
    format(src, &mut dest);
    dest
}

#[cfg(test)]
mod tests {
    use super::*;

    const TEST_CASES: [(&str, &str); 14] = [
        ("", "\n"),
        ("\n", "\n"),
        ("\n\n", "\n"),
        ("\x0b \n\t \r\n ", "\n"),
        ("* COMMENT  \n  ", "* COMMENT\n"),
        ("* COMMENT", "* COMMENT\n"),
        ("A    \n", "A\n"),
        ("A EQU  \n", "A          EQU\n"),
        ("ABCDEFGHIJ    EQU \n", "ABCDEFGHIJ EQU\n"),
        ("ABCDEFGHIJK    EQU \n", "ABCDEFGHIJK EQU\n"),
        ("ABC EQU ADDR  \n", "ABC        EQU  ADDR\n"),
        ("ABC ORIG2 ADDR  \n", "ABC        ORIG2 ADDR\n"),
        ("ABC EQU ADDR COMMENT \n", "ABC        EQU  ADDR COMMENT\n"),
        ("ABC EQU ADDR   COMMENT \n", "ABC        EQU  ADDR   COMMENT\n"),
    ];

    #[test]
    fn format_code_follows_style() {
        for (src, expected) in TEST_CASES {
            let dest1 = format_to_string(src);
            let mut dest2 = String::new();
            format(src, &mut dest2);

            assert_eq!(dest1, expected);
            assert_eq!(dest2, expected);
        }
    }
}
