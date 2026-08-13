use mixlib::ast;

#[derive(Clone, Debug)]
pub struct DocumentParse {
    ast: ast::Ast,
    errors: Vec<ast::ParseError>,
}

impl DocumentParse {
    pub fn new(text: &str) -> Self {
        let mut errors = Vec::new();
        let ast = mixlib::ast::parse(text, &mut errors);
        Self { ast, errors }
    }

    pub fn ast(&self) -> &ast::Ast {
        &self.ast
    }

    pub fn errors(&self) -> &[ast::ParseError] {
        &self.errors
    }
}
