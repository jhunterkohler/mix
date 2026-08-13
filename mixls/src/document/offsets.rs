use line_index::{LineIndex, TextSize, WideEncoding, WideLineCol};
use mixlib::source::Span;
use tower_lsp_server::ls_types::{Position, Range};

#[derive(Clone, Debug)]
pub struct DocumentOffsets {
    index: LineIndex,
}

impl DocumentOffsets {
    pub fn new(text: &str) -> Self {
        Self { index: LineIndex::new(text) }
    }

    pub fn position_to_offset(&self, pos: Position) -> Option<usize> {
        self.index
            .to_utf8(
                WideEncoding::Utf16,
                WideLineCol { col: pos.character, line: pos.line },
            )
            .and_then(|line_col| self.index.offset(line_col))
            .and_then(|offset| usize::try_from(offset).ok())
    }

    pub fn offset_to_position(&self, offset: usize) -> Option<Position> {
        TextSize::try_from(offset)
            .ok()
            .and_then(|offset| self.index.try_line_col(offset))
            .and_then(|line_col| {
                self.index.to_wide(WideEncoding::Utf16, line_col)
            })
            .map(|wide_line_col| Position {
                line: wide_line_col.line,
                character: wide_line_col.col,
            })
    }

    pub fn range_to_span(&self, range: Range) -> Option<Span> {
        self.position_to_offset(range.start)
            .zip(self.position_to_offset(range.end))
            .map(|(start, end)| Span { start, end })
    }

    pub fn span_to_range(&self, span: Span) -> Option<Range> {
        self.offset_to_position(span.start)
            .zip(self.offset_to_position(span.end))
            .map(|(start, end)| Range { start, end })
    }

    pub fn offset_to_lineno(&self, offset: usize) -> Option<usize> {
        TextSize::try_from(offset)
            .ok()
            .and_then(|offset| self.index.try_line_col(offset))
            .and_then(|line_col| usize::try_from(line_col.line).ok())
    }

    pub fn lineno_to_span(&self, lineno: usize) -> Option<Span> {
        u32::try_from(lineno)
            .ok()
            .and_then(|lineno| self.index.line(lineno))
            .and_then(|text_range| {
                usize::try_from(text_range.start())
                    .ok()
                    .zip(usize::try_from(text_range.end()).ok())
            })
            .map(|(start, end)| Span::new(start, end))
    }
}
