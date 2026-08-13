use tokio::sync::OnceCell;
use tower_lsp_server::ls_types as lsp;

mod assemble;
mod completion;
mod diagnostics;
mod formatting;
mod hovers;
mod offsets;
mod parse;
mod symbols;

use assemble::DocumentAssemble;
use diagnostics::DocumentDiagnostics;
use formatting::DocumentFormatting;
use hovers::DocumentHovers;
use offsets::DocumentOffsets;
use parse::DocumentParse;
use symbols::SymbolDb;

#[derive(Clone, Debug)]
pub struct Document {
    uri: lsp::Uri,
    version: i32,
    text: String,
    offsets: DocumentOffsets,
    parse: OnceCell<DocumentParse>,
    assemble: OnceCell<DocumentAssemble>,
    diagnostics: OnceCell<DocumentDiagnostics>,
    symbol_db: OnceCell<SymbolDb>,
    formatting: OnceCell<DocumentFormatting>,
    hovers: OnceCell<DocumentHovers>,
}

impl Document {
    pub fn new(uri: lsp::Uri, version: i32, text: String) -> Document {
        let offsets = DocumentOffsets::new(&text);

        Document {
            uri,
            version,
            text,
            offsets,
            parse: OnceCell::new(),
            assemble: OnceCell::new(),
            diagnostics: OnceCell::new(),
            symbol_db: OnceCell::new(),
            formatting: OnceCell::new(),
            hovers: OnceCell::new(),
        }
    }

    pub fn update(
        &mut self,
        version: i32,
        changes: Vec<lsp::TextDocumentContentChangeEvent>,
    ) {
        if version <= self.version {
            return;
        }

        let (partials, mut new_text) = match changes
            .into_iter()
            .rev()
            .try_fold(Vec::new(), |mut dest, change| {
                if let Some(range) = change.range {
                    dest.push((range, change.text));
                    Ok(dest)
                } else {
                    Err((dest, change.text))
                }
            }) {
            Ok(partials) => (partials, self.text.clone()),
            Err((partials, new_text)) => (partials, new_text),
        };

        let mut new_offsets = DocumentOffsets::new(&new_text);
        for (range, text) in partials {
            if let Some(span) = new_offsets.range_to_span(range) {
                new_text.replace_range(span.start..span.end, &text);
                new_offsets = DocumentOffsets::new(&new_text);
            }
        }

        self.version = version;
        self.text = new_text;
        self.offsets = new_offsets;
        self.parse.take();
        self.assemble.take();
        self.diagnostics.take();
        self.symbol_db.take();
        self.formatting.take();
        self.hovers.take();
    }

    pub fn version(&self) -> i32 {
        self.version
    }

    pub async fn get_diagnostics(&self) -> Vec<lsp::Diagnostic> {
        self.get_or_init_diagnostics().await.lsp_diagnostics().collect()
    }

    pub async fn get_references(
        &self,
        pos: lsp::Position,
        include_declaration: bool,
    ) -> Vec<lsp::Range> {
        let Some(offset) = self.offsets.position_to_offset(pos) else {
            return Vec::new();
        };

        let Some(entry) =
            self.get_or_init_symbol_db().await.symbol_entry_at(offset)
        else {
            return Vec::new();
        };

        entry
            .references()
            .filter(|sref| include_declaration || !sref.is_definition())
            .map(|sref| sref.range())
            .collect()
    }

    pub async fn get_definitions(
        &self,
        pos: lsp::Position,
    ) -> Vec<lsp::Range> {
        let Some(offset) = self.offsets.position_to_offset(pos) else {
            return Vec::new();
        };

        let Some(entry) =
            self.get_or_init_symbol_db().await.symbol_entry_at(offset)
        else {
            return Vec::new();
        };

        entry.definitions().map(|def| def.selection_range()).collect()
    }

    pub async fn get_highlights(
        &self,
        pos: lsp::Position,
    ) -> Vec<lsp::DocumentHighlight> {
        let Some(offset) = self.offsets.position_to_offset(pos) else {
            return Vec::new();
        };

        let Some(entry) =
            self.get_or_init_symbol_db().await.symbol_entry_at(offset)
        else {
            return Vec::new();
        };

        entry.references().map(|sref| sref.highlight()).collect()
    }

    pub async fn get_prepare_rename(
        &self,
        pos: lsp::Position,
    ) -> Option<lsp::Range> {
        let offset = self.offsets.position_to_offset(pos)?;
        let entry = self.get_or_init_symbol_db().await.reference_at(offset)?;

        Some(entry.range())
    }

    pub async fn get_symbols(&self) -> Vec<lsp::DocumentSymbol> {
        self.get_or_init_symbol_db()
            .await
            .symbol_entries()
            .flat_map(|entry| {
                entry.definitions().map(|def| lsp::DocumentSymbol {
                    name: entry.name().into(),
                    detail: None,
                    kind: lsp::SymbolKind::CONSTANT,
                    tags: None,
                    #[expect(deprecated)]
                    deprecated: None,
                    range: def.range(),
                    selection_range: def.selection_range(),
                    children: None,
                })
            })
            .collect()
    }

    pub async fn get_formatting(&self) -> Vec<lsp::TextEdit> {
        self.get_or_init_formatting().await.edits().collect()
    }

    pub async fn get_hover(&self, pos: lsp::Position) -> Option<lsp::Hover> {
        let offset = self.offsets.position_to_offset(pos)?;

        self.get_or_init_hovers().await.hover_at(offset).map(|hover| {
            lsp::Hover {
                contents: lsp::HoverContents::Scalar(
                    lsp::MarkedString::String(hover.contents().into()),
                ),
                range: Some(hover.range()),
            }
        })
    }

    pub async fn get_completion(
        &self,
        pos: lsp::Position,
    ) -> Option<Vec<lsp::CompletionItem>> {
        completion::document_completion(
            pos,
            &self.text,
            &self.offsets,
            self.get_or_init_symbol_db().await,
        )
    }

    async fn get_or_init_parse(&self) -> &DocumentParse {
        self.parse.get_or_init(async || DocumentParse::new(&self.text)).await
    }

    async fn get_or_init_assemble(&self) -> &DocumentAssemble {
        self.assemble
            .get_or_init(async || {
                DocumentAssemble::new(
                    &self.uri,
                    &self.text,
                    self.get_or_init_parse().await,
                )
            })
            .await
    }

    async fn get_or_init_diagnostics(&self) -> &DocumentDiagnostics {
        self.diagnostics
            .get_or_init(async || {
                DocumentDiagnostics::new(
                    &self.offsets,
                    self.get_or_init_parse().await,
                    self.get_or_init_assemble().await,
                )
            })
            .await
    }

    async fn get_or_init_symbol_db(&self) -> &SymbolDb {
        self.symbol_db
            .get_or_init(async || {
                SymbolDb::new(
                    &self.offsets,
                    self.get_or_init_parse().await,
                    self.get_or_init_assemble().await,
                )
            })
            .await
    }

    async fn get_or_init_formatting(&self) -> &DocumentFormatting {
        self.formatting
            .get_or_init(async || {
                DocumentFormatting::new(&self.text, &self.offsets)
            })
            .await
    }

    async fn get_or_init_hovers(&self) -> &DocumentHovers {
        self.hovers
            .get_or_init(async || {
                DocumentHovers::new(
                    &self.offsets,
                    self.get_or_init_parse().await,
                    self.get_or_init_assemble().await,
                )
            })
            .await
    }
}
