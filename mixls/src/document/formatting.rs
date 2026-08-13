use dissimilar::{Chunk, diff};
use mixlib::source::Span;
use tower_lsp_server::ls_types as lsp;

use crate::document::offsets::DocumentOffsets;

#[derive(Clone, Debug)]
pub struct DocumentFormatting {
    edits: Vec<lsp::TextEdit>,
}

impl DocumentFormatting {
    pub fn edits(&self) -> impl Iterator<Item = lsp::TextEdit> {
        self.edits.iter().cloned()
    }
}

impl DocumentFormatting {
    pub fn new(text: &str, offsets: &DocumentOffsets) -> Self {
        let new_text = mixlib::fmt::format_to_string(text);
        let mut offset = 0;
        let mut edits = Vec::new();

        for chunk in diff(text, &new_text) {
            match chunk {
                Chunk::Equal(part) => {
                    offset += part.len();
                }
                Chunk::Delete(part) => {
                    let new_offset = offset + part.len();
                    let span = Span::new(offset, new_offset);

                    offset = new_offset;
                    edits.push(lsp::TextEdit {
                        range: offsets.span_to_range(span).unwrap(),
                        new_text: String::new(),
                    })
                }
                Chunk::Insert(part) => {
                    let start = offsets.offset_to_position(offset).unwrap();
                    let range = lsp::Range::new(start, start);

                    edits.push(lsp::TextEdit {
                        range,
                        new_text: part.to_string(),
                    })
                }
            }
        }

        Self { edits }
    }
}
