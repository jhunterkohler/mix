use mixlib::asm;
use mixlib::ast;
use tower_lsp_server::ls_types as lsp;

use crate::constants::MIXLIB_DIAGNOSTIC_SOURCE;
use crate::document::assemble::DocumentAssemble;
use crate::document::offsets::DocumentOffsets;
use crate::document::parse::DocumentParse;

#[derive(Clone, Debug)]
pub struct DocumentDiagnosticEntry {
    range: lsp::Range,
    severity: lsp::DiagnosticSeverity,
    message: String,
}

#[derive(Clone, Debug)]
pub struct DocumentDiagnostics {
    diagnostics: Vec<DocumentDiagnosticEntry>,
}

impl DocumentDiagnostics {
    pub fn new(
        offsets: &DocumentOffsets,
        parse: &DocumentParse,
        assemble: &DocumentAssemble,
    ) -> Self {
        Factory::new(offsets, parse, assemble).create()
    }

    pub fn lsp_diagnostics(&self) -> impl Iterator<Item = lsp::Diagnostic> {
        self.diagnostics.iter().map(|diag| lsp::Diagnostic {
            range: diag.range,
            severity: Some(diag.severity),
            code: None,
            code_description: None,
            source: Some(MIXLIB_DIAGNOSTIC_SOURCE.to_string()),
            message: diag.message.clone(),
            related_information: None,
            tags: None,
            data: None,
        })
    }
}

#[derive(Clone, Debug)]
struct Factory<'a> {
    offsets: &'a DocumentOffsets,
    parse: &'a DocumentParse,
    assemble: &'a DocumentAssemble,
}

impl<'a> Factory<'a> {
    fn new(
        offsets: &'a DocumentOffsets,
        parse: &'a DocumentParse,
        assemble: &'a DocumentAssemble,
    ) -> Self {
        Self { offsets, parse, assemble }
    }

    fn create(self) -> DocumentDiagnostics {
        let diagnostics = if self.parse.errors().is_empty() {
            match self.assemble.kind() {
                Ok(_) => Vec::new(),
                Err(errors) => errors
                    .iter()
                    .map(|err| self.assembly_err_diagnostic(err))
                    .collect(),
            }
        } else {
            self.parse
                .errors()
                .iter()
                .map(|err| self.parse_err_diagnostic(err))
                .collect()
        };

        DocumentDiagnostics { diagnostics }
    }

    fn parse_err_diagnostic(
        &self,
        err: &ast::ParseError,
    ) -> DocumentDiagnosticEntry {
        DocumentDiagnosticEntry {
            range: self.offsets.span_to_range(err.span()).unwrap(),
            severity: lsp::DiagnosticSeverity::ERROR,
            message: format!("Parse Error: {err}"),
        }
    }

    fn assembly_err_diagnostic(
        &self,
        err: &asm::AssemblyError,
    ) -> DocumentDiagnosticEntry {
        DocumentDiagnosticEntry {
            range: self.offsets.span_to_range(err.span()).unwrap(),
            severity: lsp::DiagnosticSeverity::ERROR,
            message: format!("Assembly Error: {err}"),
        }
    }
}
