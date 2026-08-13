use mixlib::asm;
use mixlib::source::Span;
use mixlib::symbol::Symbol;
use tower_lsp_server::ls_types as lsp;

use crate::document::{DocumentOffsets, SymbolDb};
use crate::keyword::Keyword;

#[derive(Clone, Debug)]
struct CompletionOffsets {
    /// Offset of completion position into source text.
    text_offset: usize,
    /// Offset of completion position into line.
    line_offset: usize,
    /// Line number of completion position.
    lineno: usize,
    /// Span of line surrounding completion position.
    line_span: Span,
}

impl CompletionOffsets {
    fn at(
        pos: lsp::Position,
        offsets: &DocumentOffsets,
    ) -> Option<CompletionOffsets> {
        let text_offset = offsets.position_to_offset(pos)?;
        let lineno = usize::try_from(pos.line).ok()?;
        let line_span = offsets.lineno_to_span(lineno)?;
        let line_offset = text_offset - line_span.start;

        Some(CompletionOffsets { text_offset, lineno, line_span, line_offset })
    }
}

#[derive(Clone, Debug)]
struct CompletionLine<'a> {
    /// The word surrounding the completion position.
    word: &'a str,
    /// The inline text before `word`.
    before_word: &'a str,
    /// The inline text after `word`.
    after_word: &'a str,
}

impl<'a> CompletionLine<'a> {
    fn at(text: &'a str, offsets: &CompletionOffsets) -> Self {
        let line = &text[offsets.line_span];
        let (before_word, word, after_word) =
            split_at_word(line, offsets.line_offset);

        CompletionLine { word, before_word, after_word }
    }
}

fn split_at_word<'a>(
    text: &'a str,
    offset: usize,
) -> (&'a str, &'a str, &'a str) {
    let start = text[..offset]
        .char_indices()
        .rev()
        .take_while(|(_, c)| c.is_alphanumeric())
        .last()
        .map_or(offset, |(i, _)| i);

    let end = text[offset..]
        .char_indices()
        .take_while(|(_, c)| c.is_alphanumeric())
        .last()
        .map_or(offset, |(i, c)| i + c.len_utf8());

    let before = &text[..start];
    let word = &text[start..end];
    let after = &text[end..];

    (before, word, after)
}

fn count_ws_blocks(text: &str) -> usize {
    let mut prev_ws = false;
    let mut count = 0;

    for c in text.chars() {
        let curr_ws = c.is_whitespace();

        if curr_ws && !prev_ws {
            count += 1;
        }

        prev_ws = curr_ws;
    }

    count
}

pub fn document_completion(
    pos: lsp::Position,
    text: &str,
    doc_offsets: &DocumentOffsets,
    symbols: &SymbolDb,
) -> Option<Vec<lsp::CompletionItem>> {
    let offsets = CompletionOffsets::at(pos, doc_offsets)?;
    let line = CompletionLine::at(text, &offsets);

    if line.before_word.starts_with('*') {
        // Then, we are in a line comment.
        return None;
    }

    match count_ws_blocks(line.before_word) {
        // This is a LOC.
        0 => None,
        // This is a OP.
        1 => Some(ops_completion(line.word)),
        // This ia an ADDRESS.
        2 => Some(symbol_completion(line.word, symbols)),
        // This is a end-of-line comment.
        _ => None,
    }
}

fn ascii_starts_with_ignore_case(text: &str, item: &str) -> bool {
    for (b1, b2) in text.bytes().zip(item.bytes()) {
        if b1.to_ascii_uppercase() != b2.to_ascii_uppercase() {
            return false;
        }
    }

    true
}

fn keyword_completion<T: Keyword>(
    word: &str,
) -> impl Iterator<Item = lsp::CompletionItem> {
    T::iter()
        .filter(|kw| ascii_starts_with_ignore_case(kw.as_str(), word))
        .map(|kw| lsp::CompletionItem {
            label: kw.as_str().into(),
            kind: Some(lsp::CompletionItemKind::KEYWORD),
            documentation: Some(lsp::Documentation::String(kw.docs().into())),
            ..Default::default()
        })
}

fn ops_completion(word: &str) -> Vec<lsp::CompletionItem> {
    keyword_completion::<asm::Op>(word)
        .chain(keyword_completion::<asm::PseudoOp>(word))
        .collect()
}

fn symbol_completion(
    word: &str,
    symbols: &SymbolDb,
) -> Vec<lsp::CompletionItem> {
    symbols
        .symbol_entries()
        .filter_map(|entry| match entry.symbol() {
            Symbol::NonLocal(name)
                if ascii_starts_with_ignore_case(name.as_str(), word) =>
            {
                Some(lsp::CompletionItem {
                    label: name.as_str().into(),
                    kind: Some(lsp::CompletionItemKind::CONSTANT),
                    ..Default::default()
                })
            }
            _ => None,
        })
        .collect()
}
