use std::fmt;

use tower_lsp_server::ls_types as lsp;

#[derive(Clone, Debug)]
pub enum LogEvent {
    DidOpenUnknownLanguageId {
        uri: lsp::Uri,
        version: i32,
        language_id: String,
    },
    GoToDefinitionUnopened {
        uri: lsp::Uri,
    },
    ReferencesUnopened {
        uri: lsp::Uri,
    },
    DocumentSymbolUnopened {
        uri: lsp::Uri,
    },
    DocumentHighlightUnopened {
        uri: lsp::Uri,
    },
    FormattingUnopened {
        uri: lsp::Uri,
    },
    DidChangeUnopened {
        uri: lsp::Uri,
    },
    DidChangeOutdated {
        uri: lsp::Uri,
        current_version: i32,
        update_version: i32,
    },
    DidSaveUnopened {
        uri: lsp::Uri,
    },
    DidOpenDocumentRepeat {
        uri: lsp::Uri,
        new_version: i32,
        old_version: i32,
    },
    DidCloseUnopened {
        uri: lsp::Uri,
    },
    PrepareRenameUnopened {
        uri: lsp::Uri,
    },
    RenameUnopened {
        uri: lsp::Uri,
    },
    HoverUnopened {
        uri: lsp::Uri,
    },
    CompletionUnopened {
        uri: lsp::Uri,
    },
}

impl LogEvent {
    pub fn message_type(&self) -> lsp::MessageType {
        use LogEvent::*;
        match self {
            DidOpenUnknownLanguageId { .. } => lsp::MessageType::WARNING,
            GoToDefinitionUnopened { .. } => lsp::MessageType::WARNING,
            ReferencesUnopened { .. } => lsp::MessageType::WARNING,
            DocumentSymbolUnopened { .. } => lsp::MessageType::WARNING,
            DocumentHighlightUnopened { .. } => lsp::MessageType::WARNING,
            FormattingUnopened { .. } => lsp::MessageType::WARNING,
            DidChangeUnopened { .. } => lsp::MessageType::WARNING,
            DidChangeOutdated { .. } => lsp::MessageType::WARNING,
            DidSaveUnopened { .. } => lsp::MessageType::WARNING,
            DidOpenDocumentRepeat { .. } => lsp::MessageType::WARNING,
            DidCloseUnopened { .. } => lsp::MessageType::WARNING,
            PrepareRenameUnopened { .. } => lsp::MessageType::WARNING,
            RenameUnopened { .. } => lsp::MessageType::WARNING,
            HoverUnopened { .. } => lsp::MessageType::WARNING,
            CompletionUnopened { .. } => lsp::MessageType::WARNING,
        }
    }
}

impl fmt::Display for LogEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use LogEvent::*;
        match self {
            DidOpenUnknownLanguageId { uri, version, language_id } => f
                .write_fmt(format_args!(
                    "textDocument/didOpen recieved on {} version {version} \
                    with unknown language id {language_id}.",
                    uri.as_str()
                )),
            GoToDefinitionUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/gotoDefinition recieved on {} but it is \
                not open.",
                uri.as_str()
            )),
            ReferencesUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/references recieved on {} but it is not open.",
                uri.as_str()
            )),
            DocumentSymbolUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/documentSymbol recieved on {} but it is not \
                open.",
                uri.as_str()
            )),
            DocumentHighlightUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/documentHighlight recieved on {} but it is \
                not open.",
                uri.as_str()
            )),
            FormattingUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/formatting recieved on {} but it is not open.",
                uri.as_str()
            )),
            DidChangeUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/didChange recieved on {} but it is not open.",
                uri.as_str()
            )),
            DidChangeOutdated { uri, current_version, update_version } => f
                .write_fmt(format_args!(
                    "textDocument/didChange recieved on {} for version \
                    {update_version} when version {current_version} is \
                    already tracked.",
                    uri.as_str()
                )),
            DidSaveUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/didSave recieved on {} but it is not open.",
                uri.as_str()
            )),
            DidOpenDocumentRepeat { uri, new_version, old_version } => f
                .write_fmt(format_args!(
                    "textDocument/didOpen recieved on {} version \
                    {new_version} when version {old_version} is already \
                    opened.",
                    uri.as_str()
                )),
            DidCloseUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/didClone recieved on {} but it is not open.",
                uri.as_str()
            )),
            PrepareRenameUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/prepareRename recieved on {} but it is not \
                open.",
                uri.as_str()
            )),
            RenameUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/rename recieved on {} but it is not open.",
                uri.as_str()
            )),
            HoverUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/hover recieved on {} but it is not open.",
                uri.as_str()
            )),
            CompletionUnopened { uri } => f.write_fmt(format_args!(
                "textDocument/completion recieved on {} but it is not open.",
                uri.as_str()
            )),
        }
    }
}
