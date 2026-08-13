use std::collections::HashMap;
use std::collections::hash_map::Entry;

use mixlib::ast;
use mixlib::num::Word;
use mixlib::source::Span;
use mixlib::symbol::Symbol;
use rangemap::RangeInclusiveMap;
use tower_lsp_server::ls_types as lsp;

use crate::document::assemble::DocumentAssemble;
use crate::document::offsets::DocumentOffsets;
use crate::document::parse::DocumentParse;

#[derive(Clone, Debug)]
pub struct SymbolDef {
    range: lsp::Range,
    selection_range: lsp::Range,
}

impl SymbolDef {
    pub fn range(&self) -> lsp::Range {
        self.range
    }

    pub fn selection_range(&self) -> lsp::Range {
        self.selection_range
    }
}

#[derive(Clone, Debug)]
pub struct SymbolRef {
    is_definition: bool,
    range: lsp::Range,
}

impl SymbolRef {
    pub fn is_definition(&self) -> bool {
        self.is_definition
    }

    pub fn range(&self) -> lsp::Range {
        self.range
    }

    pub fn highlight(&self) -> lsp::DocumentHighlight {
        lsp::DocumentHighlight { range: self.range, kind: None }
    }
}

#[derive(Clone, Debug)]
pub struct SymbolDbEntry {
    name: String,
    symbol: Symbol,
    value: Option<Word>,
    definitions: Vec<SymbolDef>,
    references: Vec<SymbolRef>,
}

impl SymbolDbEntry {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn symbol(&self) -> Symbol {
        self.symbol
    }

    pub fn value(&self) -> Option<Word> {
        self.value
    }

    pub fn definitions(&self) -> impl Iterator<Item = &SymbolDef> {
        self.definitions.iter()
    }

    pub fn references(&self) -> impl Iterator<Item = &SymbolRef> {
        self.references.iter()
    }
}

#[derive(Clone, Debug, PartialEq)]
struct IndexEntry {
    /// The index of the usage in [`DocumentSymbolDatabase::entries`].
    entry_pos: usize,
    /// The index of the usage in [`DocumentSymbolEntry::references`].
    reference_pos: usize,
}

#[derive(Clone, Debug)]
pub struct SymbolDb {
    entries: Vec<SymbolDbEntry>,
    index: RangeInclusiveMap<usize, IndexEntry>,
}

impl SymbolDb {
    pub fn new(
        offsets: &DocumentOffsets,
        parse: &DocumentParse,
        assemble: &DocumentAssemble,
    ) -> Self {
        Factory::new(offsets, parse, assemble).create()
    }

    pub fn symbol_entries(&self) -> impl Iterator<Item = &SymbolDbEntry> {
        self.entries.iter()
    }

    pub fn symbol_entry_at(&self, offset: usize) -> Option<&SymbolDbEntry> {
        let index_entry = self.index.get(&offset)?;
        let symbol_entry = &self.entries[index_entry.entry_pos];

        Some(symbol_entry)
    }

    pub fn reference_at(&self, offset: usize) -> Option<&SymbolRef> {
        let index_entry = self.index.get(&offset)?;
        let symbol_entry = &self.entries[index_entry.entry_pos];
        let reference = &symbol_entry.references[index_entry.reference_pos];

        Some(reference)
    }

    fn add_entry(
        &mut self,
        offsets: &DocumentOffsets,
        assemble: &DocumentAssemble,
        factory_entry: FactorySymbolEntry,
    ) {
        let value = factory_entry.resolve_symbol_value(assemble);
        let entry_pos = self.entries.len();
        let defcount = factory_entry.definitions.len();
        let refcount = factory_entry.references.len() + defcount;
        let mut definitions = Vec::with_capacity(defcount);
        let mut references = Vec::with_capacity(refcount);

        for def in factory_entry.definitions {
            let reference_pos = references.len();
            let range = offsets.span_to_range(def.span).unwrap();
            let selection_range =
                offsets.span_to_range(def.selection_span).unwrap();
            let index_entry = IndexEntry { entry_pos, reference_pos };

            definitions.push(SymbolDef { range, selection_range });

            references.push(SymbolRef {
                range: selection_range,
                is_definition: true,
            });

            self.index.insert(def.span.start..=def.span.end, index_entry);
        }

        for span in factory_entry.references {
            let reference_pos = references.len();
            let range = offsets.span_to_range(span).unwrap();
            let index_entry = IndexEntry { entry_pos, reference_pos };

            references.push(SymbolRef { range, is_definition: false });

            self.index.insert(span.start..=span.end, index_entry)
        }

        self.entries.push(SymbolDbEntry {
            name: factory_entry.name,
            symbol: factory_entry.symbol,
            value,
            references,
            definitions,
        });
    }
}

#[derive(Clone, Debug)]
struct FactorySymbolDef {
    span: Span,
    selection_span: Span,
}

#[derive(Clone, Debug)]
struct FactorySymbolEntry {
    name: String,
    symbol: Symbol,
    definitions: Vec<FactorySymbolDef>,
    references: Vec<Span>,
}

impl FactorySymbolEntry {
    fn resolve_symbol_value(
        &self,
        assemble: &DocumentAssemble,
    ) -> Option<Word> {
        match self.definitions.len() {
            // Undefined.
            0 => Some(Word::POS_ZERO),
            // Has definition.
            1 => {
                let span = self.definitions[0].span;
                assemble
                    .kind()
                    .ok()?
                    .debug_info()
                    .symbols()
                    .iter()
                    .find(|info| info.definition() == Some(span))
                    .map(|info| info.value())
            }
            // Multiply defined.
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
struct Factory<'a> {
    offsets: &'a DocumentOffsets,
    parse: &'a DocumentParse,
    assemble: &'a DocumentAssemble,
    active_symbols: HashMap<Symbol, FactorySymbolEntry>,
    inactive_symbols: Vec<FactorySymbolEntry>,
    future_refs: HashMap<Symbol, Vec<Span>>,
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
            active_symbols: Default::default(),
            inactive_symbols: Default::default(),
            future_refs: Default::default(),
        }
    }

    fn create(mut self) -> SymbolDb {
        self.on_ast(self.parse.ast());

        let mut dest = SymbolDb {
            entries: Default::default(),
            index: Default::default(),
        };

        for entry in self.inactive_symbols {
            dest.add_entry(self.offsets, self.assemble, entry);
        }

        for (_, entry) in self.active_symbols {
            dest.add_entry(self.offsets, self.assemble, entry);
        }

        for (symbol, references) in self.future_refs {
            let entry = FactorySymbolEntry {
                name: name_undefined_symbol(symbol),
                symbol,
                definitions: vec![],
                references,
            };

            dest.add_entry(self.offsets, self.assemble, entry);
        }

        dest
    }

    fn on_ast(&mut self, ast: &ast::Ast) {
        for line in ast.lines() {
            self.on_line(line);
        }
    }

    fn on_line(&mut self, line: &ast::Line) {
        line.loc().inspect(|loc| self.on_loc(line, loc));

        match line.op_address().kind() {
            ast::OpAddressKind::Mix(mix) => self.on_mix(mix),
            ast::OpAddressKind::Equ(wvalue) => self.on_wvalue(wvalue),
            ast::OpAddressKind::Orig(wvalue) => self.on_wvalue(wvalue),
            ast::OpAddressKind::Con(wvalue) => self.on_wvalue(wvalue),
            ast::OpAddressKind::End(wvalue) => self.on_wvalue(wvalue),
            ast::OpAddressKind::Alf(_) => {}
        }
    }

    fn on_loc(&mut self, line: &ast::Line, loc: &ast::Loc) {
        let symbol = loc.symbol();
        let make_definition = || FactorySymbolDef {
            span: line.span(),
            selection_span: loc.span(),
        };

        let mut make_entry = || FactorySymbolEntry {
            name: name_symbol(&self.offsets, loc.span(), symbol),
            symbol,
            definitions: vec![make_definition()],
            references: self.future_refs.remove(&symbol).unwrap_or_default(),
        };

        match self.active_symbols.entry(symbol) {
            Entry::Occupied(mut occupied) => match symbol {
                Symbol::Local(_) => {
                    let old = occupied.insert(make_entry());
                    self.inactive_symbols.push(old);
                }
                Symbol::NonLocal(_) => {
                    occupied.get_mut().definitions.push(make_definition());
                }
            },
            Entry::Vacant(vacant) => {
                vacant.insert(make_entry());
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
            ast::APartKind::FutureRef(symbol) => {
                self.on_future_ref(a_part.span(), *symbol)
            }
            ast::APartKind::LiteralConstant(wvalue) => self.on_wvalue(wvalue),
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

    fn on_future_ref(&mut self, span: Span, symbol: Symbol) {
        match self.future_refs.entry(symbol) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut().push(span);
            }
            Entry::Vacant(vacant) => {
                vacant.insert(vec![span]);
            }
        }
    }

    fn on_expr(&mut self, expr: &ast::Expr) {
        self.on_atomic_expr(expr.head());

        for (_, atomic) in expr.tail() {
            self.on_atomic_expr(atomic);
        }
    }

    fn on_atomic_expr(&mut self, atomic: &ast::AtomicExpr) {
        if let ast::AtomicExprKind::Symbol(symbol) = *atomic.kind() {
            match self.active_symbols.entry(symbol) {
                Entry::Occupied(mut occupied) => {
                    occupied.get_mut().references.push(atomic.span());
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(FactorySymbolEntry {
                        name: name_symbol(
                            &self.offsets,
                            atomic.span(),
                            symbol,
                        ),
                        symbol,
                        definitions: Vec::new(),
                        references: vec![atomic.span()],
                    });
                }
            }
        }
    }

    fn on_wvalue(&mut self, wvalue: &ast::WValue) {
        for (expr, f_part) in wvalue.parts() {
            self.on_expr(expr);
            self.on_f_part(f_part);
        }
    }
}

fn name_symbol(
    offsets: &DocumentOffsets,
    span: Span,
    symbol: Symbol,
) -> String {
    match symbol {
        Symbol::Local(index) => {
            let lineno = offsets.offset_to_lineno(span.start).unwrap();
            format!("Local {index} (Line {lineno})")
        }
        Symbol::NonLocal(name) => name.to_string(),
    }
}

fn name_undefined_symbol(symbol: Symbol) -> String {
    match symbol {
        Symbol::Local(index) => format!("Local {index} (Undefined)"),
        Symbol::NonLocal(name) => format!("{name} (Undefined)"),
    }
}
