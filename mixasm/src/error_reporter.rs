use annotate_snippets::{Level, Message, Renderer, Snippet};
use mixlib::asm::{AssemblyError, AssemblyErrorKind};
use mixlib::ast::{ParseError, ParseErrorKind};
use mixlib::num::Word;
use mixlib::source::BytePos;

pub struct ErrorReporter<'a> {
    src: &'a str,
    origin: &'a str,
    renderer: &'a Renderer,
}

impl<'a> ErrorReporter<'a> {
    pub fn new(src: &'a str, origin: &'a str, renderer: &'a Renderer) -> Self {
        Self { src, origin, renderer }
    }

    fn display_message(&self, msg: Message<'_>) {
        eprintln!("{}", self.renderer.render(msg));
    }

    fn snippet(&self) -> Snippet<'_> {
        Snippet::source(self.src).origin(self.origin).fold(true)
    }

    pub fn report_parse_error(&self, err: &ParseError) {
        match err.kind() {
            ParseErrorKind::InvalidAlfStringBadChar(span) => {
                let bad_char = &self.src[*span];
                let title = format!("invalid string character: `{bad_char}`");
                let ann = Level::Error
                    .span(span.to_range_usize())
                    .label("invalid character");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidAlfStringTooLong => {
                let title = "invalid string, too long";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("string longer than 5 characters");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidNumberTooLong => {
                let title = "invalid number, too long";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("number longer than 10 digits");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidNumberBadChar(span) => {
                let bad_char = &self.src[*span];
                let title = format!("invalid number digits: `{bad_char}`.");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("invalid digit");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidLiteralConstantTooLong => {
                let title = "invalid literal constant, too long";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("W-value more than 9 characters");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidOp => {
                let title = "invalid operation";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("invalid operation");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidSymbolNoAlpha => {
                let title = "invalid symbol, no alphabetic character";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("no alphabetic character here");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidSymbolTooLong => {
                let title = "invalid symbol, too long";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("symbol longer than 10 characters");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidSymbolBadChar(span) => {
                let bad_char = &self.src[*span];
                let title =
                    format!("invalid symbol, bad character: `{bad_char}`");
                let ann = Level::Error
                    .span(span.to_range_usize())
                    .label("this character is invalid");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::InvalidLocalSymbol => {
                let title = "invalid local symbol";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("this form of local symbol can not be used here");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::UnclosedAlfString => {
                let title = "unclosed alf string, expected '\"'";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("string unclosed");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::UnclosedLiteralConstant => {
                let title = "unclosed literal constant, expected '='";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("literal constant unclosed");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::UnclosedFPart => {
                let title = "unclosed F-part, expected ')'";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("F-part unclosed");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::UnexpectedChar => {
                let bad_char = &self.src[err.span()];
                let title = format!("unexpected character: `{bad_char}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("unexpected character");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::UnexpectedEOF => {
                let title = "unexpected EOF";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("unexpected EOF");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::UnexpectedNewLine => {
                let title = "unexpected newline";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("unexpected newline");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            ParseErrorKind::SourceTooLong => {
                let title = format!(
                    "source length unsupported, length must be at most {}",
                    BytePos::MAX
                );
                let msg = Level::Error.title(&title);

                self.display_message(msg);
            }
            _ => unreachable!(),
        }
    }

    pub fn report_assembly_error(&self, err: &AssemblyError) {
        match err.kind() {
            AssemblyErrorKind::NoEntryPoint => {
                let title = "no entry point, expected an 'END' operation";
                let msg = Level::Error.title(title);

                self.display_message(msg);
            }
            AssemblyErrorKind::CodeAfterEnd => {
                let title = "code after 'END' operation";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("cannot have code after 'END'");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::InvalidIndex { value } => {
                let title = format!("invalid index: evaluated to `{value}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("invalid index evaluated here");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::InvalidField { op, value } => {
                let title =
                    format!("invalid field `{value}` for operation `{op}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("field evaluated here");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::UndefinedSymbol { symbol } => {
                let title = format!("undefined symbol: `{symbol}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("this symbol is undefined");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::NumberOutOfRange { number } => {
                let title = format!("number out of range: `{number}`");
                let label = format!("must be at most {}", Word::MAX);
                let ann = Level::Error.span(err.span().into()).label(&label);
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::FieldOutOfRange { value } => {
                let title = format!("field out of range: `{value}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("field evaluated here");
                let help = Level::Help
                    .title("field must be some 8 * L + R where 0 ≤ L ≤ R ≤ 5");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann))
                    .footer(help);

                self.display_message(msg);
            }
            AssemblyErrorKind::RedefinedSymbol { definition, symbol } => {
                let title = format!("redefined symbol: `{symbol}`");
                let prev = Level::Info
                    .span(definition.to_range_usize())
                    .label("symbol previously defined here");
                let curr = Level::Error
                    .span(err.span().into())
                    .label("symbol redefined here");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotations([prev, curr]));

                self.display_message(msg);
            }
            AssemblyErrorKind::MultipleDataAtAddress { address } => {
                let title = format!(
                    "multiple data stored at `{address}` while assembling"
                );
                let ann = Level::Error
                    .span(err.span().into())
                    .label("store occurred here");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::InvalidLocation { value } => {
                let title = format!("invalid location: `{value}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("evaluated here");
                let help = Level::Help
                    .title("location counter must be in between 0 and 4095");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann))
                    .footer(help);

                self.display_message(msg);
            }
            AssemblyErrorKind::InvalidEntryPoint { value } => {
                let title = format!("invalid entry point: `{value}`");
                let ann = Level::Error
                    .span(err.span().into())
                    .label("taken from the (4:5) word evaluated here");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::LocationIsInvalidAddress {
                location_counter,
            } => {
                let title = format!(
                    "attempted to store at invalid memory address \
                     `{location_counter}` during assembly"
                );
                let ann = Level::Error
                    .span(err.span().into())
                    .label("store occurred here");
                let msg = Level::Error
                    .title(&title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            AssemblyErrorKind::LocationCounterOverflow => {
                let title = "location counter overflow during assembly";
                let ann = Level::Error
                    .span(err.span().into())
                    .label("overflow occurred here");
                let msg = Level::Error
                    .title(title)
                    .snippet(self.snippet().annotation(ann));

                self.display_message(msg);
            }
            _ => unreachable!(),
        }
    }
}
