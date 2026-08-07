use std::collections::HashSet;
use std::error;
use std::fmt;
use std::str::Chars;
use std::str::FromStr;

use crate::asm::Op;
use crate::ast::*;
use crate::char::Char;
use crate::source::Span;
use crate::symbol::{SymbolIndex, SymbolName};

#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseErrorKind {
    InvalidAlfStringBadChar(Span),
    InvalidAlfStringTooLong,
    InvalidNumberTooLong,
    InvalidNumberBadChar(Span),
    InvalidLiteralConstantTooLong,
    InvalidOp,
    InvalidSymbolNoAlpha,
    InvalidSymbolTooLong,
    InvalidSymbolBadChar(Span),
    InvalidLocalSymbol,
    UnclosedAlfString,
    UnclosedLiteralConstant,
    UnclosedFPart,
    UnexpectedChar,
    UnexpectedEOF,
    UnexpectedNewLine,
    SourceTooLong,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    span: Span,
    kind: ParseErrorKind,
}

impl ParseError {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &ParseErrorKind {
        &self.kind
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use ParseErrorKind::*;
        f.write_str(match self.kind {
            InvalidAlfStringBadChar(_) => "invalid string, bad character",
            InvalidAlfStringTooLong => "invalid string, too long",
            InvalidNumberTooLong => "invalid number, too long",
            InvalidNumberBadChar(_) => "invalid number, bad character",
            InvalidLiteralConstantTooLong => "invalid constant, too long",
            InvalidOp => "invalid operator",
            InvalidSymbolNoAlpha => "invalid symbol, no letters",
            InvalidSymbolTooLong => "invalid symbol, too long",
            InvalidSymbolBadChar(_) => "invalid symbol, bad character",
            UnclosedAlfString => "unclosed alf string, expected '\"'",
            UnclosedLiteralConstant => "unclosed constant, expected '='",
            UnclosedFPart => "unclosed F-part, expected ')'",
            UnexpectedChar => "unexpected characters",
            UnexpectedEOF => "unexpected EOF",
            UnexpectedNewLine => "unexpected new line",
            InvalidLocalSymbol => "invalid local symbol usage",
            SourceTooLong => "unsupported source length",
        })
    }
}

impl error::Error for ParseError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WValueOp {
    Equ,
    Orig,
    Con,
    End,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParsedSymbolKind {
    LocalF(SymbolIndex),
    LocalH(SymbolIndex),
    LocalB(SymbolIndex),
    NonLocal(SymbolName),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedSymbol {
    span: Span,
    kind: ParsedSymbolKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedNumber {
    span: Span,
    value: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedLiteralConstant {
    span: Span,
    w_value: WValue,
}

struct Parser<'a> {
    src: &'a str,
    it: Chars<'a>,
    symbols: HashSet<Symbol>,
}

impl<'a> Parser<'a> {
    /// Create new parser.
    fn new(src: &'a str) -> Self {
        Parser { src, it: src.chars(), symbols: HashSet::new() }
    }

    /// Returns true if end of input is reached.
    fn is_eof(&self) -> bool {
        self.it.as_str().is_empty()
    }

    /// Gets current position.
    fn pos(&self) -> usize {
        self.src.len() - self.it.as_str().len()
    }

    /// Sets current position.
    fn set_pos(&mut self, pos: usize) {
        self.it = self.src[pos..].chars();
    }

    /// Get the next character of input without consuming it.
    fn peek(&self) -> Option<char> {
        self.it.clone().next()
    }

    /// Get the 2nd next character of input without consuming anything.
    fn peek2(&self) -> Option<char> {
        self.it.clone().nth(1)
    }

    /// Get the next character of input and consuming it.
    fn next(&mut self) -> Option<char> {
        self.it.next()
    }

    /// Get the span of the next character of input and consume it.
    fn next_span(&mut self) -> Option<Span> {
        let start = self.pos();
        self.next().map(|_| Span::new(start, self.pos()))
    }

    /// Consume a character of input if `f` evaluated true on it. Returns true
    /// if a character was consumed.
    fn bump_if<F: FnOnce(char) -> bool>(&mut self, f: F) -> bool {
        if self.peek().is_some_and(f) {
            self.next();
            true
        } else {
            false
        }
    }

    /// Consume a character of input if the next char is `c`. Returns true
    /// if a character was consumed.
    fn bump_if_eq(&mut self, c: char) -> bool {
        self.bump_if(|d| d == c)
    }

    /// Skip input to the start of the next line and returns the end position
    /// of the current line (before newline).
    fn skip_to_next_line(&mut self) -> usize {
        loop {
            match self.peek() {
                // "\r\n" style newline
                Some('\r') if self.peek2() == Some('\n') => {
                    let pos = self.pos();
                    self.next();
                    self.next();
                    return pos;
                }
                // "\n" style newline
                Some('\n') => {
                    let pos = self.pos();
                    self.next();
                    return pos;
                }
                None => return self.pos(),
                _ => self.next(),
            };
        }
    }

    /// Skip whitespace except for newlines.
    fn skip_inline_whitespace(&mut self) {
        loop {
            match self.peek() {
                // "\r\n" style newline
                Some('\r') if self.peek2() == Some('\n') => return,
                // "\n" style newline
                Some('\n') => return,
                Some(c) if c.is_whitespace() => self.next(),
                _ => return,
            };
        }
    }

    /// Skip non whitespace.
    fn skip_non_whitespace(&mut self) {
        while self.bump_if(|c| !c.is_whitespace()) {}
    }

    /// Generate an unexpected newline error.
    fn unexpected_newline_err(&self) -> ParseError {
        let start = self.pos();
        let end = start + 1;
        let span = Span::new(start, end);
        let kind = ParseErrorKind::UnexpectedNewLine;

        ParseError { span, kind }
    }

    /// Generate an unexpected char error.
    fn unexpected_char_err(&self, c: char) -> ParseError {
        let start = self.pos();
        let end = start + c.len_utf8();
        let span = Span::new(start, end);
        let kind = ParseErrorKind::UnexpectedChar;

        ParseError { span, kind }
    }

    /// Generate an unexpected EOF error.
    fn unexpected_eof_err(&self) -> ParseError {
        let span = Span::empty(self.pos());
        let kind = ParseErrorKind::UnexpectedEOF;

        ParseError { span, kind }
    }

    /// Generate a parse error for and unexpected char, newline, or EOF.
    fn unexpected_err(&self) -> ParseError {
        match self.peek() {
            Some('\n') => self.unexpected_newline_err(),
            Some(c) => self.unexpected_char_err(c),
            None => self.unexpected_eof_err(),
        }
    }

    /// Parse a symbol returning info about the value and type.
    fn parse_symbol(&mut self) -> Result<ParsedSymbol, ParseError> {
        let start = self.pos();
        let mut bad_char = None;
        let mut has_alpha = false;

        loop {
            match self.peek() {
                Some('A'..='Z') => {
                    self.next();
                    has_alpha = true;
                }
                Some('0'..='9') => {
                    self.next();
                }
                Some(c) if c.is_alphanumeric() => {
                    bad_char = bad_char.or(self.next_span());
                }
                _ => break,
            }
        }

        let span = Span::new(start, self.pos());
        if span.is_empty() {
            Err(self.unexpected_err())
        } else if let Some(c_span) = bad_char {
            let kind = ParseErrorKind::InvalidSymbolBadChar(c_span);
            Err(ParseError { span, kind })
        } else if span.len() > 10 {
            let kind = ParseErrorKind::InvalidSymbolTooLong;
            Err(ParseError { span, kind })
        } else if !has_alpha {
            let kind = ParseErrorKind::InvalidSymbolNoAlpha;
            Err(ParseError { span, kind })
        } else {
            let name = self.src[span].as_bytes();

            if name.len() == 2 && name[0].is_ascii_digit() {
                let index =
                    SymbolIndex::try_from((name[0] - b'0') as usize).unwrap();

                match name[1] {
                    b'B' => {
                        let kind = ParsedSymbolKind::LocalB(index);
                        return Ok(ParsedSymbol { span, kind });
                    }
                    b'H' => {
                        let kind = ParsedSymbolKind::LocalH(index);
                        return Ok(ParsedSymbol { span, kind });
                    }
                    b'F' => {
                        let kind = ParsedSymbolKind::LocalF(index);
                        return Ok(ParsedSymbol { span, kind });
                    }
                    _ => {}
                }
            }

            // SAFETY: Just checked that name is valid.
            let name = unsafe { SymbolName::from_bytes_unchecked(name) };
            let kind = ParsedSymbolKind::NonLocal(name);
            Ok(ParsedSymbol { span, kind })
        }
    }

    /// Parse a number.
    fn parse_number(&mut self) -> Result<ParsedNumber, ParseError> {
        let start = self.pos();
        let mut value = 0u64;
        let mut bad_char = None;

        loop {
            match self.peek() {
                Some(c @ '0'..='9') => {
                    value = value
                        .wrapping_mul(10)
                        .wrapping_add(c as u64 - '0' as u64);

                    self.next();
                }
                Some(c) if c.is_alphanumeric() => {
                    bad_char = bad_char.or(self.next_span());
                }
                _ => break,
            }
        }

        let span = Span::new(start, self.pos());
        if span.is_empty() {
            Err(self.unexpected_err())
        } else if let Some(c_span) = bad_char {
            let kind = ParseErrorKind::InvalidNumberBadChar(c_span);
            Err(ParseError { span, kind })
        } else if span.len() > 10 {
            let kind = ParseErrorKind::InvalidNumberTooLong;
            Err(ParseError { span, kind })
        } else {
            Ok(ParsedNumber { span, value })
        }
    }

    /// Parse an atomic expression.
    fn parse_atomic_expr(&mut self) -> Result<AtomicExpr, ParseError> {
        match self.peek() {
            Some(c) if c.is_alphanumeric() => self.atomic_num_or_sym(),
            Some('*') => Ok(AtomicExpr {
                span: self.next_span().unwrap(),
                kind: AtomicExprKind::Location,
            }),
            _ => Err(self.unexpected_err()),
        }
    }

    /// Parse an atomic number or symbol.
    fn atomic_num_or_sym(&mut self) -> Result<AtomicExpr, ParseError> {
        // Lookahead to see if the alnum group has an alphabetic character.
        let mut fwd_it = self.it.clone();
        let has_alpha = loop {
            match fwd_it.next() {
                Some(c) if c.is_alphabetic() => break true,
                Some(c) if c.is_numeric() => {}
                _ => break false,
            }
        };

        if has_alpha {
            let ParsedSymbol { span, kind } = self.parse_symbol()?;
            let symbol = match kind {
                ParsedSymbolKind::LocalB(index) => Symbol::Local(index),
                ParsedSymbolKind::NonLocal(name) => Symbol::NonLocal(name),
                ParsedSymbolKind::LocalF(_) | ParsedSymbolKind::LocalH(_) => {
                    let kind = ParseErrorKind::InvalidLocalSymbol;
                    return Err(ParseError { span, kind });
                }
            };

            Ok(AtomicExpr { span, kind: AtomicExprKind::Symbol(symbol) })
        } else {
            let ParsedNumber { span, value } = self.parse_number()?;
            Ok(AtomicExpr { span, kind: AtomicExprKind::Number(value) })
        }
    }

    /// Parse an expression.
    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.pos();
        let sign = match self.peek() {
            Some('+') => {
                self.next();
                Some(Sign::Plus)
            }
            Some('-') => {
                self.next();
                Some(Sign::Minus)
            }
            _ => None,
        };

        // let head = self.parse_atomic_expr()?;
        // let head = self.parse_atomic_expr()?;

        let head = self.parse_atomic_expr()?;
        let mut tail = Vec::new();

        while let Some(bin_op) = self.match_bin_op() {
            tail.push((bin_op, self.parse_atomic_expr()?));
        }

        Ok(Expr { span: Span::new(start, self.pos()), sign, head, tail })
    }

    /// Match binary operators if next in input.
    fn match_bin_op(&mut self) -> Option<ExprBinOp> {
        match self.peek() {
            Some('+') => {
                self.next();
                Some(ExprBinOp::Add)
            }
            Some('-') => {
                self.next();
                Some(ExprBinOp::Sub)
            }
            Some('*') => {
                self.next();
                Some(ExprBinOp::Mul)
            }
            Some('/') => {
                self.next();

                if self.bump_if_eq('/') {
                    Some(ExprBinOp::HighDiv)
                } else {
                    Some(ExprBinOp::Div)
                }
            }
            Some(':') => {
                self.next();
                Some(ExprBinOp::Colon)
            }
            _ => None,
        }
    }

    /// Parse an F-part.
    fn parse_f_part(&mut self) -> Result<FPart, ParseError> {
        let start = self.pos();

        if self.bump_if_eq('(') {
            let expr = self.parse_expr()?;

            if self.bump_if_eq(')') {
                Ok(FPart {
                    span: Span::new(start, self.pos()),
                    kind: FPartKind::Expr(Box::new(expr)),
                })
            } else {
                Err(ParseError {
                    span: Span::new(start, self.pos()),
                    kind: ParseErrorKind::UnclosedFPart,
                })
            }
        } else {
            Ok(FPart { span: Span::empty(start), kind: FPartKind::Empty })
        }
    }

    /// Parse a W-value.
    fn parse_w_value(&mut self) -> Result<WValue, ParseError> {
        let mut span = Span::empty(self.pos());
        let mut parts = Vec::with_capacity(2);

        loop {
            let expr = self.parse_expr()?;
            let f_part = self.parse_f_part()?;

            span = span.with_end(f_part.span.end);
            parts.push((expr, f_part));

            if !self.bump_if_eq(',') {
                break;
            }
        }

        Ok(WValue { span, parts })
    }

    /// Parse a literal constant.
    fn parse_literal_constant(
        &mut self,
    ) -> Result<ParsedLiteralConstant, ParseError> {
        let start = self.pos();

        if self.bump_if_eq('=') {
            let wval = self.parse_w_value()?;
            if !self.bump_if_eq('=') {
                Err(ParseError {
                    span: wval.span.with_start(start),
                    kind: ParseErrorKind::UnclosedLiteralConstant,
                })
            } else if wval.span.len() >= 10 {
                Err(ParseError {
                    span: Span::new(start, self.pos()),
                    kind: ParseErrorKind::InvalidLiteralConstantTooLong,
                })
            } else {
                Ok(ParsedLiteralConstant {
                    span: Span::new(start, self.pos()),
                    w_value: wval,
                })
            }
        } else {
            Err(self.unexpected_err())
        }
    }

    /// Parse an ALF string.
    fn parse_alf_string(&mut self) -> Result<AlfString, ParseError> {
        let start = self.pos();
        let mut chars = [Char::default(); 5];
        let mut chars_it = chars.iter_mut();
        let mut bad_char = None;

        if !self.bump_if_eq('"') {
            return Err(self.unexpected_err());
        }

        loop {
            match self.peek() {
                Some('"') => {
                    self.next();
                    break;
                }
                None | Some('\n') => {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnclosedAlfString,
                        span: Span::new(start, self.pos()),
                    });
                }
                Some(c) => match Char::from_unicode_with_replacement(c) {
                    Some(d) => {
                        self.next();
                        if let Some(dest) = chars_it.next() {
                            *dest = d;
                        }
                    }
                    None => bad_char = bad_char.or(self.next_span()),
                },
            }
        }

        let span = Span::new(start, self.pos());
        if let Some(c_span) = bad_char {
            let kind = ParseErrorKind::InvalidAlfStringBadChar(c_span);
            Err(ParseError { span, kind })
        } else if span.len() > 7 {
            let kind = ParseErrorKind::InvalidAlfStringTooLong;
            Err(ParseError { span, kind })
        } else {
            Ok(AlfString { chars, span })
        }
    }

    /// Parse an index part.
    fn parse_i_part(&mut self) -> Result<IPart, ParseError> {
        let start = self.pos();

        if self.bump_if_eq(',') {
            let expr = self.parse_expr()?;
            let span = expr.span.with_start(start);
            let kind = IPartKind::Expr(Box::new(expr));

            Ok(IPart { span, kind })
        } else {
            let span = Span::empty(start);
            let kind = IPartKind::Empty;

            Ok(IPart { span, kind })
        }
    }

    /// Parse an A-part.
    fn parse_a_part(&mut self) -> Result<APart, ParseError> {
        match self.peek() {
            Some('=') => {
                let ParsedLiteralConstant { span, w_value } =
                    self.parse_literal_constant()?;

                Ok(APart {
                    span,
                    kind: APartKind::LiteralConstant(Box::new(w_value)),
                })
            }
            Some('+') | Some('-') => {
                let expr = self.parse_expr()?;
                Ok(APart {
                    span: expr.span,
                    kind: APartKind::Expr(Box::new(expr)),
                })
            }
            Some(c) if c.is_alphanumeric() => self.optimistic_future_ref(),
            _ => Ok(APart {
                span: Span::empty(self.pos()),
                kind: APartKind::Empty,
            }),
        }
    }

    /// Parse an A-part by starting to parse a future reference optimistically.
    fn optimistic_future_ref(&mut self) -> Result<APart, ParseError> {
        // Save state for failed future ref.
        let pos = self.pos();

        if let Ok(ParsedSymbol { span, kind }) = self.parse_symbol() {
            match self.peek() {
                // Binops indicate continuation of expression.
                Some('+') | Some('-') | Some('*') | Some('/') | Some(':') => {}
                _ => match kind {
                    ParsedSymbolKind::LocalF(index) => {
                        let symbol = Symbol::Local(index);
                        let kind = APartKind::FutureRef(symbol);

                        return Ok(APart { span, kind });
                    }
                    ParsedSymbolKind::NonLocal(name) => {
                        let symbol = Symbol::NonLocal(name);

                        // Disambiguate defined symbols.
                        if !self.symbols.contains(&symbol) {
                            let kind = APartKind::FutureRef(symbol);
                            return Ok(APart { span, kind });
                        }
                    }
                    _ => {}
                },
            }
        }

        // Restore state on failture.
        self.set_pos(pos);

        let expr = self.parse_expr()?;
        Ok(APart { span: expr.span, kind: APartKind::Expr(Box::new(expr)) })
    }

    /// Parse an operation and address.
    fn parse_op_address(&mut self) -> Result<OpAddress, ParseError> {
        let start = self.pos();

        self.skip_non_whitespace();

        let op_end = self.pos();
        let op_name = &self.src[Span::new(start, op_end)];

        match op_name {
            "EQU" => self.op_address_w_value(start, WValueOp::Equ),
            "ORIG" => self.op_address_w_value(start, WValueOp::Orig),
            "CON" => self.op_address_w_value(start, WValueOp::Con),
            "END" => self.op_address_w_value(start, WValueOp::End),
            "ALF" => {
                self.skip_inline_whitespace();
                let alf_string = self.parse_alf_string()?;

                Ok(OpAddress {
                    span: alf_string.span.with_start(start),
                    kind: OpAddressKind::Alf(alf_string),
                })
            }
            _ => {
                let op = Op::from_str(op_name).map_err(|_| ParseError {
                    span: Span::new(start, op_end),
                    kind: ParseErrorKind::InvalidOp,
                })?;

                self.skip_inline_whitespace();

                let a_part = self.parse_a_part()?;
                let i_part = self.parse_i_part()?;
                let f_part = self.parse_f_part()?;

                Ok(OpAddress {
                    span: f_part.span.with_start(start),
                    kind: OpAddressKind::Mix(MixOpAddress {
                        op,
                        a_part,
                        i_part,
                        f_part,
                    }),
                })
            }
        }
    }

    /// Continue parsing an op-address EQU, ORIG, CON, or END.
    fn op_address_w_value(
        &mut self,
        start: usize,
        op: WValueOp,
    ) -> Result<OpAddress, ParseError> {
        self.skip_inline_whitespace();
        let wval = self.parse_w_value()?;

        Ok(OpAddress {
            span: wval.span.with_start(start),
            kind: match op {
                WValueOp::Equ => OpAddressKind::Equ(wval),
                WValueOp::Orig => OpAddressKind::Orig(wval),
                WValueOp::Con => OpAddressKind::Con(wval),
                WValueOp::End => OpAddressKind::End(wval),
            },
        })
    }

    /// Parse a line.
    fn parse_line(&mut self) -> Result<Option<Line>, ParseError> {
        let start = self.pos();
        let loc = match self.peek() {
            Some('*') => {
                self.skip_to_next_line();
                return Ok(None);
            }
            Some(c) if c.is_whitespace() => None,
            Some(_) => {
                let ParsedSymbol { span, kind } = self.parse_symbol()?;
                let symbol = match kind {
                    ParsedSymbolKind::LocalH(index) => Symbol::Local(index),
                    ParsedSymbolKind::NonLocal(name) => Symbol::NonLocal(name),
                    _ => {
                        let kind = ParseErrorKind::InvalidLocalSymbol;
                        return Err(ParseError { span, kind });
                    }
                };

                self.symbols.insert(symbol);
                Some(Loc { span, symbol })
            }
            None => return Ok(None),
        };

        self.skip_inline_whitespace();

        // If the line is empty, return `None`.
        if loc.is_none() && matches!(self.peek(), None | Some('\n')) {
            self.next();
            return Ok(None);
        }

        let op_address = self.parse_op_address()?;
        let end = self.skip_to_next_line();

        Ok(Some(Line { span: Span::new(start, end), loc, op_address }))
    }

    fn parse(&mut self) -> (Ast, Vec<ParseError>) {
        let mut lines = Vec::new();
        let mut errors = Vec::new();

        while !self.is_eof() {
            match self.parse_line() {
                Ok(Some(line)) => lines.push(line),
                Ok(None) => {}
                Err(e) => {
                    errors.push(e);
                    self.skip_to_next_line();
                }
            }
        }

        (Ast { lines }, errors)
    }

    /// Parse a full tree, collecting multiple errors.
    fn parse_ast(&mut self) -> Result<Ast, Vec<ParseError>> {
        let (ast, errors) = self.parse();

        if errors.is_empty() { Ok(ast) } else { Err(errors) }
    }

    /// Return error if any more characters in input. Used for solo parsing
    /// of atomic expressions, expressions, and W_values.
    fn expect_eof(&self) -> Result<(), ParseError> {
        match self.peek() {
            Some(c) => Err(self.unexpected_char_err(c)),
            None => Ok(()),
        }
    }
}

pub fn parse(src: &str, errors: &mut Vec<ParseError>) -> Ast {
    let (ast, mut new_errors) = Parser::new(src).parse();
    errors.append(&mut new_errors);
    ast
}

impl FromStr for AtomicExpr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parser = Parser::new(s);
        let atomic = parser.parse_atomic_expr()?;
        parser.expect_eof()?;
        Ok(atomic)
    }
}

impl FromStr for Expr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parser = Parser::new(s);
        let atomic = parser.parse_expr()?;
        parser.expect_eof()?;
        Ok(atomic)
    }
}

impl FromStr for WValue {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut parser = Parser::new(s);
        let atomic = parser.parse_w_value()?;
        parser.expect_eof()?;
        Ok(atomic)
    }
}

impl FromStr for Ast {
    type Err = Vec<ParseError>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Parser::new(s).parse_ast()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sym_name(name: &str) -> SymbolName {
        SymbolName::from_str(name).unwrap()
    }

    fn sym_index(index: usize) -> SymbolIndex {
        SymbolIndex::try_from(index).unwrap()
    }

    fn nonlocal_sym(name: &str) -> Symbol {
        Symbol::NonLocal(sym_name(name))
    }

    fn local_sym(index: usize) -> Symbol {
        Symbol::Local(sym_index(index))
    }

    fn atomic_sym(symbol: Symbol, span: Span) -> AtomicExpr {
        AtomicExpr { span, kind: AtomicExprKind::Symbol(symbol) }
    }

    fn atomic_num(value: u64, span: Span) -> AtomicExpr {
        AtomicExpr { span, kind: AtomicExprKind::Number(value) }
    }

    fn atomic_loc(span: Span) -> AtomicExpr {
        AtomicExpr { kind: AtomicExprKind::Location, span }
    }

    fn expr_num(value: u64, span: Span) -> Expr {
        Expr { sign: None, head: atomic_num(value, span), tail: vec![], span }
    }

    fn fpart_empty(span: Span) -> FPart {
        FPart { span, kind: FPartKind::Empty }
    }

    fn fpart_expr(expr: Expr, span: Span) -> FPart {
        FPart { span, kind: FPartKind::Expr(Box::new(expr)) }
    }

    fn w_value_num(value: u64, span: Span) -> WValue {
        WValue {
            span,
            parts: vec![(
                expr_num(value, span),
                fpart_empty(Span::empty(span.end)),
            )],
        }
    }

    #[test]
    fn parser_parse_symbol_err_unexpected_char() {
        let mut parser = Parser::new("∫");

        assert_eq!(
            parser.parse_symbol(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedChar,
                span: Span::from(0..3)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_symbol_err_unexpected_newline() {
        let mut parser = Parser::new("\n");

        assert_eq!(
            parser.parse_symbol(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedNewLine,
                span: Span::from(0..1)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_symbol_err_unexpected_eof() {
        let mut parser = Parser::new("");

        assert_eq!(
            parser.parse_symbol(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedEOF,
                span: Span::from(0..0)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_symbol_err_invalid_symbol_bad_char() {
        let mut parser = Parser::new("AΣF");

        assert_eq!(
            parser.parse_symbol(),
            Err(ParseError {
                kind: ParseErrorKind::InvalidSymbolBadChar(Span::from(1..3)),
                span: Span::from(0..4)
            })
        );
    }

    #[test]
    fn parser_parse_symbol_err_invalid_symbol_too_long() {
        let mut parser = Parser::new("ABCDEFGHIJK");

        assert_eq!(
            parser.parse_symbol(),
            Err(ParseError {
                kind: ParseErrorKind::InvalidSymbolTooLong,
                span: Span::from(0..11),
            })
        )
    }
    #[test]
    fn parser_parse_symbol_err_invalid_symbol_no_alpha() {
        let mut parser = Parser::new("0123456789");

        assert_eq!(
            parser.parse_symbol(),
            Err(ParseError {
                kind: ParseErrorKind::InvalidSymbolNoAlpha,
                span: Span::from(0..10),
            })
        )
    }

    #[test]
    fn parser_parse_symbol_ok_local() {
        for (src, kind) in [
            ("1B", ParsedSymbolKind::LocalB(sym_index(1))),
            ("1F", ParsedSymbolKind::LocalF(sym_index(1))),
            ("1H", ParsedSymbolKind::LocalH(sym_index(1))),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_symbol(),
                Ok(ParsedSymbol { span: Span::from(0..2), kind })
            )
        }
    }

    #[test]
    fn parser_parse_symbol_ok_nonlocal() {
        for (src, name) in [
            ("ABC", sym_name("ABC")),
            ("AB12", sym_name("AB12")),
            ("1A", sym_name("1A")),
            ("ABCDEFGHIJ", sym_name("ABCDEFGHIJ")),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_symbol(),
                Ok(ParsedSymbol {
                    span: Span::from(0..src.len()),
                    kind: ParsedSymbolKind::NonLocal(name)
                })
            )
        }
    }

    #[test]
    fn parser_parse_number_err_unexpected_char() {
        let mut parser = Parser::new("∫");

        assert_eq!(
            parser.parse_number(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedChar,
                span: Span::from(0..3)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_number_err_unexpected_newline() {
        let mut parser = Parser::new("\n");

        assert_eq!(
            parser.parse_number(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedNewLine,
                span: Span::from(0..1)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_number_err_unexpected_eof() {
        let mut parser = Parser::new("");

        assert_eq!(
            parser.parse_number(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedEOF,
                span: Span::from(0..0)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_number_err_invalid_number_bad_char() {
        let mut parser = Parser::new("123A4B");

        assert_eq!(
            parser.parse_number(),
            Err(ParseError {
                span: Span::from(0..6),
                kind: ParseErrorKind::InvalidNumberBadChar(Span::from(3..4))
            })
        );
    }

    #[test]
    fn parser_parse_number_err_invalid_number_too_long() {
        let mut parser = Parser::new("01234567890");

        assert_eq!(
            parser.parse_number(),
            Err(ParseError {
                span: Span::from(0..11),
                kind: ParseErrorKind::InvalidNumberTooLong
            })
        );
    }

    #[test]
    fn parser_parse_number_ok() {
        for (src, value) in [
            ("0", 0),
            ("123", 123),
            ("000123", 123),
            ("9876543210", 9876543210),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_number(),
                Ok(ParsedNumber { span: Span::from(0..src.len()), value })
            );
        }
    }

    #[test]
    fn parser_parse_atomic_expr_fail_in_symbol() {
        assert!(Parser::new("ABCDEFGHIJK").parse_atomic_expr().is_err());
    }

    #[test]
    fn parser_parse_atomic_expr_fail_in_number() {
        assert!(Parser::new("00000000000").parse_atomic_expr().is_err());
    }

    #[test]
    fn parser_parse_atomic_expr_err_unexpected_char() {
        let mut parser = Parser::new("∫");

        assert_eq!(
            parser.parse_atomic_expr(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedChar,
                span: Span::from(0..3)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_atomic_expr_err_unexpected_newline() {
        let mut parser = Parser::new("\n");

        assert_eq!(
            parser.parse_atomic_expr(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedNewLine,
                span: Span::from(0..1)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_atomic_expr_err_unexpected_eof() {
        let mut parser = Parser::new("");

        assert_eq!(
            parser.parse_atomic_expr(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedEOF,
                span: Span::from(0..0)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_atomic_expr_err_invalid_local_symbol() {
        for src in ["1F", "1H"] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_atomic_expr(),
                Err(ParseError {
                    span: Span::from(0..2),
                    kind: ParseErrorKind::InvalidLocalSymbol
                })
            )
        }
    }

    #[test]
    fn parser_parse_atomic_expr_ok() {
        for (src, atomic_expr) in [
            ("*", atomic_loc(Span::from(0..1))),
            ("ABC", atomic_sym(nonlocal_sym("ABC"), Span::from(0..3))),
            ("1B", atomic_sym(local_sym(1), Span::from(0..2))),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_atomic_expr(), Ok(atomic_expr));
        }
    }

    #[test]
    fn parser_parse_expr_fail_in_head() {
        assert!(Parser::new("1F").parse_expr().is_err());
    }

    #[test]
    fn parser_parse_expr_fail_in_tail() {
        assert!(Parser::new("0+1F").parse_expr().is_err());
    }

    #[test]
    fn parser_parse_expr_ok() {
        for (src, expr) in [
            (
                "-1+2-3*4/5//6:7",
                Expr {
                    span: Span::from(0..15),
                    sign: Some(Sign::Minus),
                    head: atomic_num(1, Span::from(1..2)),
                    tail: [
                        (ExprBinOp::Add, atomic_num(2, Span::from(3..4))),
                        (ExprBinOp::Sub, atomic_num(3, Span::from(5..6))),
                        (ExprBinOp::Mul, atomic_num(4, Span::from(7..8))),
                        (ExprBinOp::Div, atomic_num(5, Span::from(9..10))),
                        (
                            ExprBinOp::HighDiv,
                            atomic_num(6, Span::from(12..13)),
                        ),
                        (ExprBinOp::Colon, atomic_num(7, Span::from(14..15))),
                    ]
                    .into(),
                },
            ),
            (
                "+1",
                Expr {
                    span: Span::from(0..2),
                    sign: Some(Sign::Plus),
                    head: atomic_num(1, Span::from(1..2)),
                    tail: vec![],
                },
            ),
            (
                "1",
                Expr {
                    span: Span::from(0..1),
                    sign: None,
                    head: atomic_num(1, Span::from(0..1)),
                    tail: vec![],
                },
            ),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_expr(), Ok(expr));
        }
    }

    #[test]
    fn parser_parse_f_part_fail_in_expr() {
        assert!(Parser::new("(1F)").parse_f_part().is_err());
    }

    #[test]
    fn parser_parse_f_part_err_unclosed_f_part() {
        let mut parser = Parser::new("(1");

        assert_eq!(
            parser.parse_f_part(),
            Err(ParseError {
                span: Span::from(0..2),
                kind: ParseErrorKind::UnclosedFPart
            })
        );
    }

    #[test]
    fn parser_parse_f_part_ok() {
        for (src, kind) in [
            ("", FPartKind::Empty),
            ("(1)", FPartKind::Expr(expr_num(1, Span::from(1..2)).into())),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_f_part(),
                Ok(FPart { span: Span::from(0..src.len()), kind })
            );
        }
    }

    #[test]
    fn parser_parse_w_value_fail_in_head_expr() {
        assert!(Parser::new("1F").parse_w_value().is_err());
    }

    #[test]
    fn parser_parse_w_value_fail_in_head_f_part() {
        assert!(Parser::new("0(1F)").parse_w_value().is_err());
    }

    #[test]
    fn parser_parse_w_value_fail_in_tail_expr() {
        assert!(Parser::new("0,1F").parse_w_value().is_err());
    }

    #[test]
    fn parser_parse_w_value_fail_in_tail_f_part() {
        assert!(Parser::new("0,0(1F)").parse_w_value().is_err());
    }

    #[test]
    fn parser_parse_w_value_ok() {
        for (src, w_value) in [
            (
                "1",
                WValue {
                    span: Span::from(0..1),
                    parts: vec![(
                        expr_num(1, Span::from(0..1)),
                        fpart_empty(Span::from(1..1)),
                    )],
                },
            ),
            (
                "1(2)",
                WValue {
                    span: Span::from(0..4),
                    parts: vec![(
                        expr_num(1, Span::from(0..1)),
                        fpart_expr(
                            expr_num(2, Span::from(2..3)),
                            Span::from(1..4),
                        ),
                    )],
                },
            ),
            (
                "1(2),3(4)",
                WValue {
                    span: Span::from(0..9),
                    parts: vec![
                        (
                            expr_num(1, Span::from(0..1)),
                            fpart_expr(
                                expr_num(2, Span::from(2..3)),
                                Span::from(1..4),
                            ),
                        ),
                        (
                            expr_num(3, Span::from(5..6)),
                            fpart_expr(
                                expr_num(4, Span::from(7..8)),
                                Span::from(6..9),
                            ),
                        ),
                    ],
                },
            ),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_w_value(), Ok(w_value));
        }
    }

    #[test]
    fn parser_parse_literal_constant_fail_in_w_value() {
        assert!(Parser::new("=1F=").parse_literal_constant().is_err());
    }

    #[test]
    fn parser_parse_literal_constant_err_unexpected_char() {
        let mut parser = Parser::new("∫");

        assert_eq!(
            parser.parse_literal_constant(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedChar,
                span: Span::from(0..3)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_literal_constant_err_unexpected_newline() {
        let mut parser = Parser::new("\n");

        assert_eq!(
            parser.parse_literal_constant(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedNewLine,
                span: Span::from(0..1)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_literal_constant_err_unexpected_eof() {
        let mut parser = Parser::new("");

        assert_eq!(
            parser.parse_literal_constant(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedEOF,
                span: Span::from(0..0)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_literal_constant_err_unclosed_literal_constant() {
        let mut parser = Parser::new("=1");

        assert_eq!(
            parser.parse_literal_constant(),
            Err(ParseError {
                kind: ParseErrorKind::UnclosedLiteralConstant,
                span: Span::from(0..2)
            })
        );
    }

    #[test]
    fn parser_parse_literal_constant_err_invalid_literal_constant_too_long() {
        let mut parser = Parser::new("=0123456789=");

        assert_eq!(
            parser.parse_literal_constant(),
            Err(ParseError {
                kind: ParseErrorKind::InvalidLiteralConstantTooLong,
                span: Span::from(0..12)
            })
        );
    }

    #[test]
    fn parse_parse_literal_constant_ok() {
        let mut parser = Parser::new("=123456789=");

        assert_eq!(
            parser.parse_literal_constant(),
            Ok(ParsedLiteralConstant {
                span: Span::from(0..11),
                w_value: WValue {
                    span: Span::from(1..10),
                    parts: vec![(
                        expr_num(123456789, Span::from(1..10)),
                        fpart_empty(Span::from(10..10))
                    )],
                }
            })
        )
    }

    #[test]
    fn parser_parse_alf_string_err_unexpected_char() {
        let mut parser = Parser::new("∫");

        assert_eq!(
            parser.parse_alf_string(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedChar,
                span: Span::from(0..3)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_alf_string_err_unexpected_newline() {
        let mut parser = Parser::new("\n");

        assert_eq!(
            parser.parse_alf_string(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedNewLine,
                span: Span::from(0..1)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_alf_string_err_unexpected_eof() {
        let mut parser = Parser::new("");

        assert_eq!(
            parser.parse_alf_string(),
            Err(ParseError {
                kind: ParseErrorKind::UnexpectedEOF,
                span: Span::from(0..0)
            })
        );

        assert_eq!(parser.pos(), 0);
    }

    #[test]
    fn parser_parse_alf_string_err_unclosed_alf_string() {
        for src in ["\"\n", "\""] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_alf_string(),
                Err(ParseError {
                    span: Span::from(0..1),
                    kind: ParseErrorKind::UnclosedAlfString
                })
            );
        }
    }

    #[test]
    fn parser_parse_alf_string_err_invalid_alf_string_bad_char() {
        let mut parser = Parser::new("\"1x2y3z4\"");

        assert_eq!(
            parser.parse_alf_string(),
            Err(ParseError {
                span: Span::from(0..9),
                kind: ParseErrorKind::InvalidAlfStringBadChar(Span::from(
                    2..3
                ))
            })
        );
    }

    #[test]
    fn parser_parse_alf_string_err_invalid_alf_string_too_long() {
        let mut parser = Parser::new("\"ABCDEF\"");

        assert_eq!(
            parser.parse_alf_string(),
            Err(ParseError {
                span: Span::from(0..8),
                kind: ParseErrorKind::InvalidAlfStringTooLong
            })
        );
    }

    #[test]
    fn parser_parse_alf_string_ok() {
        for (src, alf_string) in [
            (
                "\"\"",
                AlfString { chars: [Char::Space; 5], span: Span::from(0..2) },
            ),
            (
                "\"ABCDE\"",
                AlfString {
                    chars: [
                        Char::CapitalA,
                        Char::CapitalB,
                        Char::CapitalC,
                        Char::CapitalD,
                        Char::CapitalE,
                    ],
                    span: Span::from(0..7),
                },
            ),
            (
                "\"Σ[\"",
                AlfString {
                    chars: [
                        Char::CapitalSigma,
                        Char::CapitalSigma,
                        Char::Space,
                        Char::Space,
                        Char::Space,
                    ],
                    span: Span::from(0..5),
                },
            ),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_alf_string(), Ok(alf_string));
        }
    }

    #[test]
    fn parser_parse_index_part_fail_in_expr() {
        assert!(Parser::new(",1F").parse_i_part().is_err());
    }

    #[test]
    fn parser_parse_index_part_ok() {
        for (src, kind) in [
            ("", IPartKind::Empty),
            (",1", IPartKind::Expr(expr_num(1, Span::from(1..2)).into())),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_i_part(),
                Ok(IPart { span: Span::from(0..src.len()), kind })
            );
        }
    }

    #[test]
    fn parser_parse_a_part_fail_in_literal_constant() {
        assert!(Parser::new("=1F=").parse_a_part().is_err());
    }

    #[test]
    fn parser_parse_a_part_fail_in_expr() {
        assert!(Parser::new("+1F").parse_expr().is_err());
        assert!(Parser::new("1u").parse_expr().is_err());
    }

    #[test]
    fn parser_parse_a_part_ok() {
        for (src, a_part) in [
            (
                "=1=",
                APart {
                    span: Span::from(0..3),
                    kind: APartKind::LiteralConstant(Box::new(w_value_num(
                        1,
                        Span::from(1..2),
                    ))),
                },
            ),
            (
                "+1",
                APart {
                    span: Span::from(0..2),
                    kind: APartKind::Expr(Box::new(Expr {
                        span: Span::from(0..2),
                        sign: Some(Sign::Plus),
                        head: atomic_num(1, Span::from(1..2)),
                        tail: vec![],
                    })),
                },
            ),
            (
                "DEF",
                APart {
                    span: Span::from(0..3),
                    kind: APartKind::Expr(Box::new(Expr {
                        span: Span::from(0..3),
                        sign: None,
                        head: atomic_sym(
                            nonlocal_sym("DEF"),
                            Span::from(0..3),
                        ),
                        tail: vec![],
                    })),
                },
            ),
            (
                "UNDEF+0",
                APart {
                    span: Span::from(0..7),
                    kind: APartKind::Expr(Box::new(Expr {
                        span: Span::from(0..7),
                        sign: None,
                        head: atomic_sym(
                            nonlocal_sym("UNDEF"),
                            Span::from(0..5),
                        ),
                        tail: vec![(
                            ExprBinOp::Add,
                            atomic_num(0, Span::from(6..7)),
                        )],
                    })),
                },
            ),
            (
                "UNDEF",
                APart {
                    span: Span::from(0..5),
                    kind: APartKind::FutureRef(nonlocal_sym("UNDEF")),
                },
            ),
            (
                "1B",
                APart {
                    span: Span::from(0..2),
                    kind: APartKind::Expr(Box::new(Expr {
                        span: Span::from(0..2),
                        sign: None,
                        head: atomic_sym(local_sym(1), Span::from(0..2)),
                        tail: vec![],
                    })),
                },
            ),
            (
                "2B",
                APart {
                    span: Span::from(0..2),
                    kind: APartKind::Expr(Box::new(Expr {
                        span: Span::from(0..2),
                        sign: None,
                        head: atomic_sym(local_sym(2), Span::from(0..2)),
                        tail: vec![],
                    })),
                },
            ),
            (
                "1F",
                APart {
                    span: Span::from(0..2),
                    kind: APartKind::FutureRef(local_sym(1)),
                },
            ),
            ("", APart { span: Span::from(0..0), kind: APartKind::Empty }),
        ] {
            let mut parser = Parser::new(src);

            parser.symbols.insert(local_sym(1));
            parser.symbols.insert(nonlocal_sym("DEF"));

            assert_eq!(parser.parse_a_part(), Ok(a_part));
        }
    }

    #[test]
    fn parser_parse_op_address_fail_in_w_value() {
        for src in ["EQU 1F", "ORIG 1F", "CON 1F", "END 1F"] {
            assert!(Parser::new(src).parse_op_address().is_err());
        }
    }

    #[test]
    fn parser_parse_op_address_fail_in_alf_string() {
        assert!(Parser::new("ALF ").parse_op_address().is_err());
    }

    #[test]
    fn parser_parse_op_address_fail_in_a_part() {
        assert!(Parser::new("ADD 01234567890").parse_op_address().is_err());
    }

    #[test]
    fn parser_parse_op_address_fail_in_index_part() {
        assert!(Parser::new("ADD 0,1F").parse_op_address().is_err());
    }

    #[test]
    fn parser_parse_op_address_fail_in_f_part() {
        assert!(Parser::new("ADD 0(1F)").parse_op_address().is_err());
    }

    #[test]
    fn parser_parse_op_address_err_invalid_op() {
        for src in ["ADD1", "ADD.", "BAD"] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_op_address(),
                Err(ParseError {
                    span: Span::from(0..src.len()),
                    kind: ParseErrorKind::InvalidOp
                })
            )
        }
    }

    #[test]
    fn parser_parse_op_address_ok() {
        for (src, op_address) in [
            (
                "EQU \t 0",
                OpAddress {
                    span: Span::from(0..7),
                    kind: OpAddressKind::Equ(w_value_num(0, Span::from(6..7))),
                },
            ),
            (
                "CON \t 0",
                OpAddress {
                    span: Span::from(0..7),
                    kind: OpAddressKind::Con(w_value_num(0, Span::from(6..7))),
                },
            ),
            (
                "END \t 0",
                OpAddress {
                    span: Span::from(0..7),
                    kind: OpAddressKind::End(w_value_num(0, Span::from(6..7))),
                },
            ),
            (
                "ORIG \t0",
                OpAddress {
                    span: Span::from(0..7),
                    kind: OpAddressKind::Orig(w_value_num(
                        0,
                        Span::from(6..7),
                    )),
                },
            ),
            (
                "ALF \t \"\"",
                OpAddress {
                    span: Span::from(0..8),
                    kind: OpAddressKind::Alf(AlfString {
                        span: Span::from(6..8),
                        chars: [Char::Space; 5],
                    }),
                },
            ),
            (
                "MUL \t 0,1(2)",
                OpAddress {
                    span: Span::from(0..12),
                    kind: OpAddressKind::Mix(MixOpAddress {
                        op: Op::MUL,
                        a_part: APart {
                            span: Span::from(6..7),
                            kind: APartKind::Expr(Box::new(expr_num(
                                0,
                                Span::from(6..7),
                            ))),
                        },
                        i_part: IPart {
                            span: Span::from(7..9),
                            kind: IPartKind::Expr(Box::new(expr_num(
                                1,
                                Span::from(8..9),
                            ))),
                        },
                        f_part: FPart {
                            span: Span::from(9..12),
                            kind: FPartKind::Expr(Box::new(expr_num(
                                2,
                                Span::from(10..11),
                            ))),
                        },
                    }),
                },
            ),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_op_address(), Ok(op_address));
        }
    }

    #[test]
    fn parser_parse_line_fail_in_loc_parse_symbol() {
        assert!(Parser::new("x ADD 0").parse_line().is_err());
    }

    #[test]
    fn parser_parse_line_fail_in_parse_op_address() {
        assert!(Parser::new(" BAD 0").parse_line().is_err());
    }

    #[test]
    fn parser_parse_line_err_invalid_local_symbol() {
        for src in ["1B ADD 0", "1F ADD 0"] {
            let mut parser = Parser::new(src);

            assert_eq!(
                parser.parse_line(),
                Err(ParseError {
                    span: Span::from(0..2),
                    kind: ParseErrorKind::InvalidLocalSymbol
                })
            );
        }
    }

    #[test]
    fn parser_parse_line_ok_comment() {
        let mut parser = Parser::new("* COMMENT \n");

        assert_eq!(parser.parse_line(), Ok(None));
        assert_eq!(parser.pos(), 11);
    }

    #[test]
    fn parser_parse_line_ok_empty() {
        for (src, pos) in [("\t \r \n", 5), ("\t \r ", 4)] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_line(), Ok(None));
            assert_eq!(parser.pos(), pos);
        }
    }

    #[test]
    fn parser_parse_line_ok_newlines() {
        for (src, span) in [
            (" EQU 0", Span::from(0..6)),
            (" EQU \r 0", Span::from(0..8)),
            (" EQU 0\n", Span::from(0..6)),
            (" EQU 0\r\n", Span::from(0..6)),
            (" EQU 0\r\r\n", Span::from(0..7)),
        ] {
            let mut parser = Parser::new(src);
            let line = parser.parse_line().unwrap().unwrap();

            assert_eq!(line.span, span);
        }
    }

    #[test]
    fn parser_parse_line_ok() {
        for (src, line) in [
            (
                "1H EQU 0 comment",
                Line {
                    loc: Some(Loc {
                        span: Span::from(0..2),
                        symbol: local_sym(1),
                    }),
                    op_address: OpAddress {
                        span: Span::from(3..8),
                        kind: OpAddressKind::Equ(w_value_num(
                            0,
                            Span::from(7..8),
                        )),
                    },
                    span: Span::from(0..16),
                },
            ),
            (
                "SY EQU 0 comment",
                Line {
                    loc: Some(Loc {
                        span: Span::from(0..2),
                        symbol: nonlocal_sym("SY"),
                    }),
                    op_address: OpAddress {
                        span: Span::from(3..8),
                        kind: OpAddressKind::Equ(w_value_num(
                            0,
                            Span::from(7..8),
                        )),
                    },
                    span: Span::from(0..16),
                },
            ),
            (
                "   EQU 0 comment",
                Line {
                    loc: None,
                    op_address: OpAddress {
                        span: Span::from(3..8),
                        kind: OpAddressKind::Equ(w_value_num(
                            0,
                            Span::from(7..8),
                        )),
                    },
                    span: Span::from(0..16),
                },
            ),
        ] {
            let mut parser = Parser::new(src);

            assert_eq!(parser.parse_line(), Ok(Some(line)));
        }
    }

    #[test]
    fn parser_parse_ast_err() {
        let mut parser = Parser::new("1F ADD 0\n* COMMENT \n BAD \n");

        assert_eq!(
            parser.parse_ast(),
            Err(vec![
                ParseError {
                    span: Span::from(0..2),
                    kind: ParseErrorKind::InvalidLocalSymbol
                },
                ParseError {
                    span: Span::from(21..24),
                    kind: ParseErrorKind::InvalidOp
                }
            ])
        );

        assert!(parser.is_eof());
    }

    #[test]
    fn parser_parse_ast_ok() {
        let mut parser = Parser::new("L EQU 0 comment\n* COMMENT \n CON 0 \n");

        assert_eq!(parser.parse_ast().unwrap().lines.len(), 2);
    }
}
