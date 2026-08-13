use mixlib::asm;
use mixlib::ast;
use mixlib::source::Span;
use rangemap::RangeInclusiveMap;
use tower_lsp_server::ls_types as lsp;

use crate::document::{
    assemble::DocumentAssemble, offsets::DocumentOffsets, parse::DocumentParse,
};

#[derive(Clone, Debug, PartialEq)]
pub struct DocumentHoverEntry {
    contents: String,
    range: lsp::Range,
}

impl DocumentHoverEntry {
    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn range(&self) -> lsp::Range {
        self.range
    }
}

#[derive(Clone, Debug)]
pub struct DocumentHovers {
    hovers: Vec<DocumentHoverEntry>,
    hovers_lookup: RangeInclusiveMap<usize, usize>,
}

impl DocumentHovers {
    pub fn new(
        offsets: &DocumentOffsets,
        parse: &DocumentParse,
        assemble: &DocumentAssemble,
    ) -> Self {
        Factory::new(offsets, parse, assemble).create()
    }

    pub fn hover_at(&self, offset: usize) -> Option<&DocumentHoverEntry> {
        let index = self.hovers_lookup.get(&offset)?;
        let hover = self.hovers.get(*index)?;
        Some(hover)
    }
}

#[derive(Clone, Debug)]
struct Factory<'a> {
    offsets: &'a DocumentOffsets,
    parse: &'a DocumentParse,
    assemble: &'a DocumentAssemble,
    hovers: Vec<DocumentHoverEntry>,
    hovers_lookup: RangeInclusiveMap<usize, usize>,
}

impl<'a> Factory<'a> {
    fn new(
        offsets: &'a DocumentOffsets,
        parse: &'a DocumentParse,
        assemble: &'a DocumentAssemble,
    ) -> Self {
        Self {
            offsets,
            parse,
            assemble,
            hovers: Default::default(),
            hovers_lookup: Default::default(),
        }
    }

    fn create(mut self) -> DocumentHovers {
        for line in self.parse.ast().lines() {
            self.on_line(line);
        }

        DocumentHovers {
            hovers: self.hovers,
            hovers_lookup: self.hovers_lookup,
        }
    }

    fn get_program(&self) -> Option<&asm::Program> {
        self.assemble.kind().ok()
    }

    fn add_hover(&mut self, span: Span, contents: String) {
        self.add_hover_with_range(span, span, contents);
    }

    fn add_hover_with_range(
        &mut self,
        lookup_span: Span,
        range_span: Span,
        contents: String,
    ) {
        let index = self.hovers.len();
        let range = self.offsets.span_to_range(range_span).unwrap();
        self.hovers.push(DocumentHoverEntry { contents, range });
        self.hovers_lookup.insert(lookup_span.start..=lookup_span.end, index);
    }

    fn add_op_hover(&mut self, opaddr: &ast::OpAddress, op: asm::Op) {
        let end = opaddr.span().start + op.as_str().len();
        let span = opaddr.span().with_end(end);
        let contents = format!(
            "{}\n---\nCode = `{}`, Field = `{}`, Time = `{}u`\n",
            op.docs(),
            op.opcode().to_byte().to_u8(),
            op.default_field().to_u8(),
            op.execution_time(),
        );

        self.add_hover(span, contents);
    }

    fn add_psuedo_op_hover(
        &mut self,
        opaddr: &ast::OpAddress,
        psuedo_op: asm::PseudoOp,
    ) {
        let end = opaddr.span().start + psuedo_op.as_str().len();
        let span = opaddr.span().with_end(end);
        let contents = psuedo_op.docs().to_string();

        self.add_hover(span, contents);
    }

    fn add_symbol_hover(&mut self, span: Span) {
        if let Some(info) = self.get_program().and_then(|program| {
            program.debug_info().symbols().iter().find(|info| {
                info.references().contains(&span)
                    || info.definition() == Some(span)
            })
        }) {
            let value = info.value();
            self.add_hover(span, format!("Symbol: value = {value}"));
        }
    }

    fn add_location_hover(&mut self, span: Span) {
        if let Some(info) = self.get_program().and_then(|program| {
            program
                .debug_info()
                .location_literals()
                .iter()
                .find(|info| info.span() == span)
        }) {
            let value = info.value();
            self.add_hover(
                span,
                format!("Location literal: value = {value}\n"),
            );
        }
    }

    fn add_alf_hover(&mut self, alf: &ast::AlfString) {
        let [c1, c2, c3, c4, c5] = alf.chars().map(|c| {
            match c.to_unicode() {
                // Use non-breaking whitespace to stop markdown compressing
                // spaces.
                ' ' => '\u{A0}',
                u => u,
            }
        });

        let contents =
            format!("String literal: value = `{c1}{c2}{c3}{c4}{c5}`");
        self.add_hover(alf.span(), contents);
    }

    fn add_number_hover(&mut self, span: Span, value: u64) {
        let contents = format!("Number literal: value = {value}");
        self.add_hover(span, contents);
    }

    fn add_literal_contant_hover(&mut self, ast: &ast::APart) {
        let definition_span = ast.span();
        let start_span = definition_span.with_end(definition_span.start + 1);
        let end_span = definition_span.with_start(definition_span.end - 1);

        if let Some(info) = self.get_program().and_then(|program| {
            program
                .debug_info()
                .literal_constants()
                .iter()
                .find(|info| info.definition() == definition_span)
        }) {
            let address = info.address();
            let value = info.value();
            let contents = format!(
                "Literal constant: value = {value}, address = {address}"
            );

            // Hover for starting `=`.
            self.add_hover_with_range(
                start_span,
                definition_span,
                contents.clone(),
            );

            // Hover for ending `=`.
            self.add_hover_with_range(end_span, definition_span, contents);
        }
    }

    fn on_line(&mut self, line: &ast::Line) {
        line.loc().inspect(|loc| self.on_loc(loc));
        self.on_op_address(line.op_address());
    }

    fn on_loc(&mut self, loc: &ast::Loc) {
        self.add_symbol_hover(loc.span());
    }

    fn on_op_address(&mut self, oa: &ast::OpAddress) {
        match oa.kind() {
            ast::OpAddressKind::Mix(mix) => {
                self.add_op_hover(oa, mix.op());
                self.on_mix(mix);
            }
            ast::OpAddressKind::Equ(wvalue) => {
                self.add_psuedo_op_hover(oa, asm::PseudoOp::EQU);
                self.on_wvalue(wvalue);
            }
            ast::OpAddressKind::Orig(wvalue) => {
                self.add_psuedo_op_hover(oa, asm::PseudoOp::ORIG);
                self.on_wvalue(wvalue);
            }
            ast::OpAddressKind::Con(wvalue) => {
                self.add_psuedo_op_hover(oa, asm::PseudoOp::CON);
                self.on_wvalue(wvalue);
            }
            ast::OpAddressKind::End(wvalue) => {
                self.add_psuedo_op_hover(oa, asm::PseudoOp::END);
                self.on_wvalue(wvalue);
            }
            ast::OpAddressKind::Alf(alfstring) => {
                self.add_psuedo_op_hover(oa, asm::PseudoOp::ALF);
                self.add_alf_hover(alfstring);
            }
        }
    }

    fn on_wvalue(&mut self, wvalue: &ast::WValue) {
        for (expr, fpart) in wvalue.parts() {
            self.on_expr(expr);
            self.on_f_part(fpart);
        }
    }

    fn on_expr(&mut self, expr: &ast::Expr) {
        self.on_atomic_expr(expr.head());

        for (_, atomic) in expr.tail() {
            self.on_atomic_expr(atomic);
        }
    }

    fn on_atomic_expr(&mut self, atomic: &ast::AtomicExpr) {
        match atomic.kind() {
            ast::AtomicExprKind::Location => {
                self.add_location_hover(atomic.span())
            }
            ast::AtomicExprKind::Symbol(_) => {
                self.add_symbol_hover(atomic.span())
            }
            ast::AtomicExprKind::Number(value) => {
                self.add_number_hover(atomic.span(), *value)
            }
        }
    }

    fn on_mix(&mut self, mix: &ast::MixOpAddress) {
        self.on_a_part(mix.a_part());
        self.on_i_part(mix.i_part());
        self.on_f_part(mix.f_part());
    }

    fn on_a_part(&mut self, a_part: &ast::APart) {
        match a_part.kind() {
            ast::APartKind::Empty => {}
            ast::APartKind::Expr(expr) => self.on_expr(expr),
            ast::APartKind::FutureRef(_) => {
                self.add_symbol_hover(a_part.span())
            }
            ast::APartKind::LiteralConstant(wvalue) => {
                self.on_wvalue(wvalue);
                self.add_literal_contant_hover(a_part);
            }
        }
    }

    fn on_i_part(&mut self, i_part: &ast::IPart) {
        match i_part.kind() {
            ast::IPartKind::Empty => {}
            ast::IPartKind::Expr(expr) => self.on_expr(expr),
        }
    }

    fn on_f_part(&mut self, f_part: &ast::FPart) {
        match f_part.kind() {
            ast::FPartKind::Empty => {}
            ast::FPartKind::Expr(expr) => self.on_expr(expr),
        }
    }
}
