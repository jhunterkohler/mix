use mixlib::asm;
use tower_lsp_server::ls_types as lsp;

use crate::document::parse::DocumentParse;

#[derive(Clone, Debug)]
pub struct DocumentAssemble {
    kind: Result<asm::Program, Vec<asm::AssemblyError>>,
}

impl DocumentAssemble {
    pub fn new(uri: &lsp::Uri, text: &str, parse: &DocumentParse) -> Self {
        let path = uri.to_file_path().map(|path| path.to_path_buf());
        let kind = mixlib::asm::assemble(parse.ast(), text, path);

        Self { kind }
    }

    pub fn kind(&self) -> Result<&asm::Program, &[asm::AssemblyError]> {
        self.kind.as_ref().map_err(Vec::as_slice)
    }
}
