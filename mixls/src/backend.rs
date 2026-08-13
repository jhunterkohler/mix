use std::collections::HashMap;

use dashmap::{DashMap, Entry};
use tower_lsp_server::jsonrpc::Result;
use tower_lsp_server::ls_types::{
    CompletionOptions, CompletionParams, CompletionResponse,
    DidChangeTextDocumentParams, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, DidSaveTextDocumentParams,
    DocumentFormattingParams, DocumentHighlight, DocumentHighlightParams,
    DocumentSymbolParams, DocumentSymbolResponse, GotoDefinitionParams,
    GotoDefinitionResponse, Hover, HoverParams, HoverProviderCapability,
    InitializeParams, InitializeResult, Location, OneOf, PositionEncodingKind,
    PrepareRenameResponse, ReferenceContext, ReferenceParams, RenameOptions,
    RenameParams, SaveOptions, ServerCapabilities, ServerInfo,
    TextDocumentIdentifier, TextDocumentItem, TextDocumentPositionParams,
    TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    TextDocumentSyncSaveOptions, TextEdit, Uri,
    VersionedTextDocumentIdentifier, WorkspaceEdit,
};
use tower_lsp_server::{Client, LanguageServer};

use crate::constants::{MIXAL_LANGUAGE_ID, MIXLS_NAME, MIXLS_VERSION};
use crate::document::Document;
use crate::log::LogEvent;

#[derive(Debug)]
pub struct Backend {
    client: Client,
    documents: DashMap<Uri, Document>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self { client, documents: DashMap::new() }
    }

    async fn log(&self, event: LogEvent) {
        self.client.log_message(event.message_type(), event).await;
    }
}

impl LanguageServer for Backend {
    async fn initialize(
        &self,
        _params: InitializeParams,
    ) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                position_encoding: Some(PositionEncodingKind::UTF16),
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        change: Some(TextDocumentSyncKind::FULL),
                        open_close: Some(true),
                        save: Some(TextDocumentSyncSaveOptions::SaveOptions(
                            SaveOptions { include_text: Some(false) },
                        )),
                        ..Default::default()
                    },
                )),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                document_highlight_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: Default::default(),
                })),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    ..Default::default()
                }),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: MIXLS_NAME.into(),
                version: Some(MIXLS_VERSION.into()),
            }),
            // An unnecessary non-standard extension.
            offset_encoding: None,
        })
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let TextDocumentItem { uri, language_id, version, text } =
            params.text_document;

        if language_id != MIXAL_LANGUAGE_ID {
            //  Log warning, but ultimately ignore document.
            let msg = LogEvent::DidOpenUnknownLanguageId {
                language_id,
                uri,
                version,
            };
            return self.log(msg).await;
        }

        match self.documents.entry(uri) {
            Entry::Occupied(occupied) => {
                let old_version = occupied.get().version();
                self.log(LogEvent::DidOpenDocumentRepeat {
                    uri: occupied.into_key(),
                    new_version: version,
                    old_version,
                })
                .await;
                todo!()
            }
            Entry::Vacant(vacant) => {
                let info = Document::new(vacant.key().clone(), version, text);
                vacant.insert(info);
            }
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let VersionedTextDocumentIdentifier { uri, version } =
            params.text_document;

        // Mutable reference is exclusive. Likely guarantees server order
        // consistency in general.
        if let Some(mut mut_docref) = self.documents.get_mut(&uri) {
            let current_version = mut_docref.version();
            if current_version < version {
                mut_docref.update(version, params.content_changes);
            } else {
                let msg = LogEvent::DidChangeOutdated {
                    uri,
                    current_version,
                    update_version: version,
                };
                self.log(msg).await;
            }
        } else {
            let msg = LogEvent::DidChangeUnopened { uri };
            self.log(msg).await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let TextDocumentIdentifier { uri } = params.text_document;

        if let Some((_, document)) = self.documents.remove(&uri) {
            // Clear diagnostics.
            let version = Some(document.version());
            self.client.publish_diagnostics(uri, Vec::new(), version).await;
        } else {
            self.log(LogEvent::DidCloseUnopened { uri }).await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let TextDocumentIdentifier { uri } = params.text_document;

        if let Some(document) = self.documents.get(&uri) {
            // Publish new diagnostics.
            let diagnostics = document.get_diagnostics().await;
            let version = Some(document.version());
            self.client.publish_diagnostics(uri, diagnostics, version).await;
        } else {
            self.log(LogEvent::DidSaveUnopened { uri }).await;
        }
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let TextDocumentPositionParams { position, .. } =
            params.text_document_position_params;
        let TextDocumentIdentifier { uri } =
            params.text_document_position_params.text_document;

        if let Some(document) = self.documents.get(&uri) {
            let definitions: Vec<_> = document
                .get_definitions(position)
                .await
                .into_iter()
                .map(|range| Location { uri: uri.clone(), range })
                .collect();

            Ok(Some(definitions.into()))
        } else {
            self.log(LogEvent::GoToDefinitionUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn references(
        &self,
        params: ReferenceParams,
    ) -> Result<Option<Vec<Location>>> {
        let TextDocumentPositionParams { position, .. } =
            params.text_document_position;
        let TextDocumentIdentifier { uri } =
            params.text_document_position.text_document;
        let ReferenceContext { include_declaration } = params.context;

        if let Some(document) = self.documents.get(&uri) {
            let references = document
                .get_references(position, include_declaration)
                .await
                .into_iter()
                .map(|range| Location { uri: uri.clone(), range })
                .collect();

            Ok(Some(references))
        } else {
            self.log(LogEvent::ReferencesUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let TextDocumentIdentifier { uri } = params.text_document;

        if let Some(document) = self.documents.get(&uri) {
            let symbols = document.get_symbols().await;
            Ok(Some(symbols.into()))
        } else {
            self.log(LogEvent::DocumentSymbolUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn document_highlight(
        &self,
        params: DocumentHighlightParams,
    ) -> Result<Option<Vec<DocumentHighlight>>> {
        let TextDocumentPositionParams { position, text_document } =
            params.text_document_position_params;
        let TextDocumentIdentifier { uri } = text_document;

        if let Some(document) = self.documents.get(&uri) {
            let highlights = document.get_highlights(position).await;
            Ok(Some(highlights))
        } else {
            self.log(LogEvent::DocumentHighlightUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn formatting(
        &self,
        params: DocumentFormattingParams,
    ) -> Result<Option<Vec<TextEdit>>> {
        let TextDocumentIdentifier { uri } = params.text_document;

        if let Some(document) = self.documents.get(&uri) {
            let edits = document.get_formatting().await;
            Ok(Some(edits))
        } else {
            self.log(LogEvent::FormattingUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        let TextDocumentPositionParams { text_document, position } = params;
        let TextDocumentIdentifier { uri } = text_document;

        if let Some(document) = self.documents.get(&uri) {
            Ok(document
                .get_prepare_rename(position)
                .await
                .map(PrepareRenameResponse::Range))
        } else {
            self.log(LogEvent::PrepareRenameUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn rename(
        &self,
        params: RenameParams,
    ) -> Result<Option<WorkspaceEdit>> {
        let RenameParams { new_name, .. } = params;
        let TextDocumentPositionParams { text_document, position } =
            params.text_document_position;
        let TextDocumentIdentifier { uri } = text_document;

        if let Some(document) = self.documents.get(&uri) {
            let edits = document
                .get_references(position, true)
                .await
                .into_iter()
                .map(|range| TextEdit { range, new_text: new_name.clone() })
                .collect();

            let mut changes = HashMap::with_capacity(1);
            changes.insert(uri, edits);

            let workspace_edit =
                WorkspaceEdit { changes: Some(changes), ..Default::default() };

            Ok(Some(workspace_edit))
        } else {
            self.log(LogEvent::RenameUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let TextDocumentPositionParams { text_document, position } =
            params.text_document_position_params;
        let TextDocumentIdentifier { uri } = text_document;

        if let Some(document) = self.documents.get(&uri) {
            Ok(document.get_hover(position).await)
        } else {
            self.log(LogEvent::HoverUnopened { uri }).await;
            Ok(None)
        }
    }

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> Result<Option<CompletionResponse>> {
        let CompletionParams { text_document_position, .. } = params;
        let TextDocumentPositionParams { text_document, position } =
            text_document_position;
        let TextDocumentIdentifier { uri } = text_document;

        if let Some(document) = self.documents.get(&uri) {
            Ok(document.get_completion(position).await.map(Into::into))
        } else {
            self.log(LogEvent::CompletionUnopened { uri }).await;
            Ok(None)
        }
    }
}
