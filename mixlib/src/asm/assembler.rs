use siphasher::sip::SipHasher13;

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::error::Error;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::path::PathBuf;

use crate::asm::{Instruction, InvalidInstructionErrorKind, Op};
use crate::ast::*;
use crate::mem::MemoryAddress;
use crate::num::{Byte, FieldSpec, LocationCounter, Sign, Word};
use crate::source::Span;
use crate::symbol::{Symbol, SymbolName};
use crate::word;

use super::*;

/// Enum storing the type of an error that can arise during assembly.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssemblyErrorKind {
    /// No entry point was given in the program. That is, no `END` instruction
    /// was encountered before assembly completed.
    NoEntryPoint,
    /// There was lines of code after `END` was encountered.
    CodeAfterEnd,
    /// An invalid index value was encountered.
    InvalidIndex {
        /// The evaluated index.
        value: Word,
    },
    /// An invalid field value was encountered for a given MIX operation.
    InvalidField {
        /// The MIX operation being assembled during the error.
        op: Op,
        /// The evaluated field.
        value: Word,
    },
    /// An undefined symbol was referenced during evaluation.
    UndefinedSymbol {
        /// The symbol found to be undefined.
        symbol: Symbol,
    },
    /// A literal number was found to be out of the range of [`Word`].
    NumberOutOfRange {
        /// The raw literal number value.
        number: u64,
    },
    /// A W-value field was out of range. That is, it was an invalid field
    /// specification.
    FieldOutOfRange {
        /// The evaluated value of the field.
        value: Word,
    },
    /// A non-local symbol was redefined.
    RedefinedNonLocalSymbol {
        /// The first definition of the symbol.
        definition: Span,
        /// The symbol name being redefined.
        name: SymbolName,
    },
    /// The assembler attempted to place multiple pieces of data at an address.
    MultipleDataAtAddress {
        /// The memory address attempted to be assembled to.
        address: MemoryAddress,
    },
    /// An invalid location counter value was given after `ORIG`.
    InvalidLocation {
        /// The evaluated W-value.
        value: Word,
    },
    /// The (4:5) field of the W-value after `END` did not correspond to a
    /// valid memory address.
    InvalidEntryPoint {
        /// The (4:5) field of the evaluated W-value.
        value: Word,
    },
    /// An operation required storing data while the assembler's location
    /// counter was not a valid memory address.
    LocationIsInvalidAddress {
        /// The current location counter in the assembly process.
        location_counter: LocationCounter,
    },
    /// The location counter overflowed during assembly.
    LocationCounterOverflow,
}

/// An error that can arise during assembly.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AssemblyError {
    span: Span,
    kind: AssemblyErrorKind,
}

impl AssemblyError {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &AssemblyErrorKind {
        &self.kind
    }
}

impl fmt::Display for AssemblyError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            AssemblyErrorKind::NoEntryPoint => {
                f.write_str("No entry point. Expected a `END` statement.")
            }
            AssemblyErrorKind::CodeAfterEnd => {
                f.write_str("Code after `END` statement is invalid.")
            }
            AssemblyErrorKind::InvalidIndex { value } => {
                f.write_fmt(format_args!("Index value {value} is invalid."))
            }
            AssemblyErrorKind::InvalidField { op, value } => {
                f.write_fmt(format_args!(
                    "Field value {value} is invalid for operation {op}."
                ))
            }
            AssemblyErrorKind::UndefinedSymbol { symbol } => match symbol {
                Symbol::Local(index) => f.write_fmt(format_args!(
                    "Undefined local symbol {index}."
                )),
                Symbol::NonLocal(name) => f.write_fmt(format_args!(
                    "Undefined nonlocal symbol {name}."
                )),
            },
            AssemblyErrorKind::NumberOutOfRange { number } => f.write_fmt(
                format_args!("Number out of range with value {number}"),
            ),
            AssemblyErrorKind::FieldOutOfRange { value } => f.write_fmt(
                format_args!("Field out of range with value {value}"),
            ),
            AssemblyErrorKind::RedefinedNonLocalSymbol { name, .. } => {
                f.write_fmt(format_args!("Redefined non-local symbol {name}."))
            }
            AssemblyErrorKind::MultipleDataAtAddress { address } => f
                .write_fmt(format_args!(
                    "Assembler tried to write multiple times to memory at {address}."
                )),
            AssemblyErrorKind::InvalidLocation { value } => {
                f.write_fmt(format_args!(
                    "Invalid location {value}."
                ))
            },
            AssemblyErrorKind::InvalidEntryPoint { value } => {
                f.write_fmt(format_args!(
                    "Invalid entry point {value}."
                ))
            },
            AssemblyErrorKind::LocationIsInvalidAddress {
                location_counter,
            } => {
                f.write_fmt(format_args!("Location counter is an invalid address with value {location_counter}."))
            },
            AssemblyErrorKind::LocationCounterOverflow => {
                f.write_fmt(format_args!("Location counter overflowed during assembly."))
            },
        }
    }
}

impl Error for AssemblyError {}

/// Information regarding a literal constant that needs to be updated after
/// `END` is seen and then added to the debug info list. Used internally during
/// assembly.
#[derive(Debug)]
struct LiteralConstantInsert {
    /// Literal constant source span.
    definition: Span,
    /// The computed value of the constant.
    value: Word,
    pos: DataPos,
}

/// Information regarding a future reference that needs to be updated when/if
/// the symbol is defined and then added to appropriate debug info reference
/// lists. Used internally during assembly.
#[derive(Debug)]
struct FutureRefInsert {
    reference: Span,
    pos: DataPos,
}

/// Return value of of Assembler::push_data operation.
#[derive(Debug)]
struct DataInfo {
    /// Address of data.
    address: MemoryAddress,
    pos: DataPos,
}

/// Position of a piece of data in assembly.
#[derive(Debug)]
struct DataPos {
    /// Index in `Assembler::sections`.
    section_index: usize,
    /// Index in `Assembler::sections[self.section_index].data`.
    section_offset: usize,
}

#[derive(Debug)]
struct ActiveSymbolInfo {
    definition: Span,
    references: Vec<Span>,
    value: Word,
}

impl ActiveSymbolInfo {
    fn into_debug_info(self, symbol: Symbol) -> SymbolDebugInfo {
        SymbolDebugInfo {
            definition: Some(self.definition),
            references: self.references,
            value: self.value,
            symbol,
        }
    }
}

/// A temporary struct used and moved from during assembly.
#[derive(Debug)]
struct Assembler<'a> {
    /// Source syntax tree.
    ast: &'a Ast,
    /// Source code.
    source: &'a str,
    /// The source file path if given.
    source_path: Option<PathBuf>,
    /// A map between memory addresses and source lines
    source_map: HashMap<MemoryAddress, Span>,
    /// Assembled sections.
    sections: Vec<ProgramSection>,
    /// If this is `None`, then `END` has not yet been seen.
    entry_point: Option<MemoryAddress>,
    /// Inactive defined symbols.
    inactive_symbols: Vec<SymbolDebugInfo>,
    /// Active defined symbols.
    active_symbols: HashMap<Symbol, ActiveSymbolInfo>,
    /// Future reference inserts.
    future_ref_inserts: HashMap<Symbol, Vec<FutureRefInsert>>,
    /// Literal constant inserts.
    literal_constant_inserts: Vec<LiteralConstantInsert>,
    /// Literal constant debug info, populated on `END`.
    literal_constants: Vec<LiteralConstantDebugInfo>,
    /// All the strings declares so far with `ALF`.
    strings: Vec<AlfStringDebugInfo>,
    /// Constants declared so far with `CON`.
    constants: Vec<ConstantDebugInfo>,
    /// All location literals '*' in atomic expressions.
    location_literals: Vec<LocationLiteralDebugInfo>,
    /// The current location counter during the assembly process.
    location_counter: LocationCounter,
    /// Errors during assembly.
    errors: Vec<AssemblyError>,
}

/// Hash source code for assembly.
fn hash_source(src: &str) -> u64 {
    // Using one time randomly generated keys since security is not a concern.
    // We must use a non-standard package, here `siphasher`, since
    // `std::hash::DefaultHasher` makes no guarantees about consistency of
    // outputs across releases.
    let mut hasher =
        SipHasher13::new_with_keys(0xb9f80d9b0b1aa9e3, 0x9bd2e4c0fd861e91);

    // A way to ensure that ABI is broken intentionally for major versions.
    env!("CARGO_PKG_VERSION_MAJOR").hash(&mut hasher);

    src.hash(&mut hasher);
    hasher.finish()
}

impl<'a> Assembler<'a> {
    fn new(
        ast: &'a Ast,
        source: &'a str,
        source_path: Option<PathBuf>,
    ) -> Self {
        Self {
            ast,
            source,
            source_path,
            source_map: Default::default(),
            sections: vec![ProgramSection {
                address: MemoryAddress::default(),
                data: Vec::new(),
            }],
            entry_point: Default::default(),
            inactive_symbols: Default::default(),
            active_symbols: Default::default(),
            future_ref_inserts: Default::default(),
            literal_constants: Default::default(),
            literal_constant_inserts: Default::default(),
            strings: Default::default(),
            constants: Default::default(),
            location_literals: Default::default(),
            location_counter: Default::default(),
            errors: Default::default(),
        }
    }

    /// Add a `CodeAfterEnd` error.
    fn err_code_after_end(&mut self, lines: &[Line]) {
        let start = lines.first().unwrap().span().start;
        let end = lines.last().unwrap().span().end;
        let span = Span::new(start, end);
        let kind = AssemblyErrorKind::CodeAfterEnd;

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add a `NoEntryPoint` error.
    fn err_no_entry_point(&mut self) {
        let end =
            self.ast.lines().last().map(|l| l.span().end).unwrap_or_default();
        let span = Span::empty(end);
        let kind = AssemblyErrorKind::NoEntryPoint;

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add an `InvalidLocation` error.
    fn err_invalid_location(&mut self, w_value: &WValue, value: Word) {
        let span = w_value.span();
        let kind = AssemblyErrorKind::InvalidLocation { value };

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add an `LocationIsInvalidAddress` error.
    fn err_location_is_invalid_address(&mut self, line: &Line) {
        let span = line.span();
        let kind = AssemblyErrorKind::LocationIsInvalidAddress {
            location_counter: self.location_counter,
        };

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add a `MultipleDataAtAddress` error.
    fn err_multiple_data_at_address(
        &mut self,
        line: &Line,
        address: MemoryAddress,
    ) {
        let span = line.span();
        let kind = AssemblyErrorKind::MultipleDataAtAddress { address };

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add a `RedefinedSymbol` error.
    fn err_redefined_symbol(
        &mut self,
        loc: &Loc,
        name: SymbolName,
        definition: Span,
    ) {
        let span = loc.span();
        let kind =
            AssemblyErrorKind::RedefinedNonLocalSymbol { definition, name };

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add a `UndefinedSymbol` error.
    fn err_undefined_symbol(
        &mut self,
        atomic_expr: &AtomicExpr,
        symbol: Symbol,
    ) {
        let span = atomic_expr.span();
        let kind = AssemblyErrorKind::UndefinedSymbol { symbol };

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add a `NumberOutOfRange` error.
    fn err_number_out_of_range(
        &mut self,
        atomic_expr: &AtomicExpr,
        number: u64,
    ) {
        let span = atomic_expr.span();
        let kind = AssemblyErrorKind::NumberOutOfRange { number };

        self.errors.push(AssemblyError { span, kind });
    }

    /// Add a `FieldOutOfRange` error.
    fn err_field_out_of_range(&mut self, f_part: &FPart, value: Word) {
        let span = f_part.span();
        let kind = AssemblyErrorKind::FieldOutOfRange { value };

        self.errors.push(AssemblyError { span, kind })
    }

    /// Add an `InvalidField` error.
    fn err_invalid_field(&mut self, mix: &MixOpAddress, value: Word) {
        let span = mix.f_part().span();
        let kind = AssemblyErrorKind::InvalidField { op: mix.op(), value };

        self.errors.push(AssemblyError { span, kind })
    }

    /// Add an `InvalidIndex` error.
    fn err_invalid_index(&mut self, mix: &MixOpAddress, value: Word) {
        let span = mix.i_part().span();
        let kind = AssemblyErrorKind::InvalidIndex { value };

        self.errors.push(AssemblyError { span, kind })
    }

    /// Add an `InvalidEntryPoint` error.
    fn err_invalid_entry_point(&mut self, w_value: &WValue, value: Word) {
        let span = w_value.span();
        let kind = AssemblyErrorKind::InvalidEntryPoint { value };

        self.errors.push(AssemblyError { span, kind })
    }

    fn err_location_counter_overflow(&mut self, line: &Line) {
        let span = line.span();
        let kind = AssemblyErrorKind::LocationCounterOverflow;

        self.errors.push(AssemblyError { span, kind })
    }

    /// One time assemble given the `Assembler`'s configuration.
    fn assemble(mut self) -> Result<Program, Vec<AssemblyError>> {
        let mut lines = self.ast.lines();

        while !lines.is_empty() {
            if self.entry_point.is_some() {
                self.err_code_after_end(lines);
                return Err(self.errors);
            }

            self.assemble_line(&lines[0]);
            lines = &lines[1..];
        }

        match self.entry_point {
            Some(entry_point) if self.errors.is_empty() => {
                Ok(self.finish_with_no_errors(entry_point))
            }
            Some(_) => Err(self.errors),
            None => {
                self.err_no_entry_point();
                Err(self.errors)
            }
        }
    }

    /// Finish assembly by building the output `Program` once we are sure that
    /// no errors have occurred.
    fn finish_with_no_errors(self, entry_point: MemoryAddress) -> Program {
        // These conditions should be satisfied after `END` is encountered.
        debug_assert!(self.future_ref_inserts.is_empty());
        debug_assert!(self.literal_constant_inserts.is_empty());

        let debug_info = {
            let mut symbols = self.inactive_symbols;

            symbols.extend(
                self.active_symbols
                    .into_iter()
                    .map(|(symbol, info)| info.into_debug_info(symbol)),
            );

            ProgramDebugInfo {
                source_map: self.source_map,
                source_path: self.source_path,
                source_hash: hash_source(self.source),
                symbols,
                constants: self.constants,
                literal_constants: self.literal_constants,
                strings: self.strings,
                location_literals: self.location_literals,
            }
        };

        let sections = self
            .sections
            .into_iter()
            .filter(|section| !section.data.is_empty())
            .collect();

        Program { entry_point, sections, debug_info }
    }

    /// Assemble the next line. `END` must have not already been encountered.
    fn assemble_line(&mut self, line: &Line) {
        debug_assert!(self.entry_point.is_none());

        match line.op_address().kind() {
            OpAddressKind::Mix(mix) => self.assemble_mix(line, mix),
            OpAddressKind::Equ(w_value) => self.assemble_equ(line, w_value),
            OpAddressKind::Orig(w_value) => self.assemble_orig(line, w_value),
            OpAddressKind::Con(w_value) => self.assemble_con(line, w_value),
            OpAddressKind::End(w_value) => self.assemble_end(line, w_value),
            OpAddressKind::Alf(alf_string) => {
                self.assemble_alf(line, alf_string);
            }
        }
    }

    /// Assemble the line given it uses a MIX operator.
    fn assemble_mix(&mut self, line: &Line, moa: &MixOpAddress) {
        let a_part_val = self.eval_a_part(moa.a_part()).unwrap_or_default();
        let i_part_val = self.eval_i_part(moa.i_part()).unwrap_or_default();
        let f_part_val = self.eval_f_part(moa.f_part()).unwrap_or_default();
        let mut raw_inst = Word::from(Byte::from(moa.op().opcode()))
            .with_address(a_part_val)
            .with_index(i_part_val)
            .with_field(f_part_val);

        let literal_constant_val = match moa.a_part().kind() {
            APartKind::LiteralConstant(w_value) => {
                Some(self.eval_w_value(w_value).unwrap_or_default())
            }
            _ => None,
        };

        // Must occur after all evaluations.
        self.maybe_define_symbol(line.loc(), self.location_counter.into());

        if let Err(e) = Instruction::try_from(raw_inst) {
            raw_inst = Word::POS_ZERO;
            match e.kind() {
                InvalidInstructionErrorKind::InvalidField => {
                    self.err_invalid_field(moa, f_part_val);
                }
                InvalidInstructionErrorKind::InvalidIndex => {
                    self.err_invalid_index(moa, i_part_val);
                }
            }
        }

        if let Ok(data_info) = self.push_data(line, raw_inst) {
            match moa.a_part().kind() {
                APartKind::FutureRef(symbol) => {
                    let reference = moa.a_part().span();
                    let pos = data_info.pos;
                    let insert = FutureRefInsert { reference, pos };

                    self.future_ref_inserts
                        .entry(*symbol)
                        .or_default()
                        .push(insert);
                }
                APartKind::LiteralConstant(_) => {
                    let definition = moa.a_part().span();
                    let pos = data_info.pos;
                    let value = literal_constant_val.unwrap();
                    let insert =
                        LiteralConstantInsert { definition, value, pos };

                    self.literal_constant_inserts.push(insert);
                }
                _ => {}
            }
        }
    }

    /// Assemble the line given it uses the `EQU` operation.
    fn assemble_equ(&mut self, line: &Line, w_value: &WValue) {
        let value = self.eval_w_value(w_value).unwrap_or_default();
        self.maybe_define_symbol(line.loc(), value);
    }

    /// Assemble the line given it uses the `ORIG` operation.
    fn assemble_orig(&mut self, line: &Line, w_value: &WValue) {
        // Note that we don't increment the location counter after changing.
        let new_location = self.eval_w_value(w_value).unwrap_or_default();

        // Set the LOC alias before location is changed, but after evaluation.
        self.maybe_define_symbol(line.loc(), self.location_counter.into());

        match LocationCounter::try_from(new_location) {
            Ok(value) => self.location_counter = value,
            Err(_) => self.err_invalid_location(w_value, new_location),
        }
    }

    /// Assemble the line given it uses the `CON` operation.
    fn assemble_con(&mut self, line: &Line, w_value: &WValue) {
        let value = self.eval_w_value(w_value).unwrap_or_default();

        // Must define symbol after evaluation, but before location counter
        // is changed.
        self.maybe_define_symbol(line.loc(), self.location_counter.into());

        if let Ok(data_info) = self.push_data(line, value) {
            self.constants.push(ConstantDebugInfo {
                definition: w_value.span(),
                address: data_info.address,
                value,
            });
        }
    }

    /// Assemble the line given it uses the `ALF` operation.
    fn assemble_alf(&mut self, line: &Line, alf_string: &AlfString) {
        self.maybe_define_symbol(line.loc(), self.location_counter.into());

        let bytes = alf_string.chars().map(Byte::from);
        let value = Word::from_sign_bytes(Sign::Plus, bytes);

        if let Ok(data_info) = self.push_data(line, value) {
            self.strings.push(AlfStringDebugInfo {
                definition: alf_string.span(),
                address: data_info.address,
                chars: alf_string.chars(),
            });
        }
    }

    /// Assemble the line given it uses the `END` operation.
    fn assemble_end(&mut self, line: &Line, w_value: &WValue) {
        // Calculate the entry point: the (4:5) of the w-value.
        let [.., b4, b5] =
            self.eval_w_value(w_value).unwrap_or_default().bytes();

        let entry_word = Word::from_sign_bytes(
            Sign::Plus,
            [Byte::MIN, Byte::MIN, Byte::MIN, b4, b5],
        );

        let entry_point =
            MemoryAddress::try_from(entry_word).unwrap_or_else(|_| {
                self.err_invalid_entry_point(w_value, entry_word);
                MemoryAddress::MIN
            });

        self.entry_point = Some(entry_point);

        // Symbol gets the first location after inserted words. This must be
        // done before insertions because existing future references may
        // refer to this symbol.
        if let Some(loc) = line.loc() {
            let offset = self.literal_constant_inserts.len()
                + self.future_ref_inserts.len()
                - self.future_ref_inserts.contains_key(&loc.symbol()) as usize;

            match offset
                .checked_add(self.location_counter.to_usize())
                .and_then(|sum| LocationCounter::try_from(sum).ok())
            {
                Some(value) => self.define_symbol(loc, value.into()),
                None => {
                    self.err_location_counter_overflow(line);

                    // The resolution below will only give an error to the
                    // same effect as counter overflow.
                    return;
                }
            }
        }

        // Short circuit errors during insertion.
        let _ = self
            .insert_future_refs(line)
            .and_then(|_| self.insert_literal_constants(line));
    }

    /// Set the address field of the insert position to value.
    fn fixup_insert(&mut self, pos: DataPos, value: Word) {
        let target =
            &mut self.sections[pos.section_index].data[pos.section_offset];

        *target = target.with_address(value);
    }

    fn insert_future_refs(&mut self, line: &Line) -> Result<(), ()> {
        for (symbol, inserts) in mem::take(&mut self.future_ref_inserts) {
            // Symbol gets address of a zero word pushed to data.
            let value = self.push_data(line, Word::default())?.address.into();
            let mut references = Vec::with_capacity(inserts.len());

            for insert in inserts {
                references.push(insert.reference);
                self.fixup_insert(insert.pos, value);
            }

            let debug_info = SymbolDebugInfo {
                definition: None,
                symbol,
                references,
                value,
            };

            self.inactive_symbols.push(debug_info);
        }

        Ok(())
    }

    fn insert_literal_constants(&mut self, line: &Line) -> Result<(), ()> {
        for insert in mem::take(&mut self.literal_constant_inserts) {
            let address = self.push_data(line, insert.value)?.address;
            let debug_info = LiteralConstantDebugInfo {
                definition: insert.definition,
                value: insert.value,
                address,
            };

            self.fixup_insert(insert.pos, address.into());
            self.literal_constants.push(debug_info);
        }

        Ok(())
    }

    /// Evaluate an atomic expression.
    fn eval_atomic_expr(
        &mut self,
        atomic_expr: &AtomicExpr,
    ) -> Result<Word, ()> {
        match atomic_expr.kind() {
            AtomicExprKind::Location => {
                self.location_literals.push(LocationLiteralDebugInfo {
                    span: atomic_expr.span(),
                    value: self.location_counter,
                });

                Ok(self.location_counter.into())
            }
            AtomicExprKind::Symbol(symbol) => {
                match self.active_symbols.get_mut(symbol) {
                    Some(info) => {
                        info.references.push(atomic_expr.span());
                        Ok(info.value)
                    }
                    None => {
                        self.err_undefined_symbol(atomic_expr, *symbol);
                        Err(())
                    }
                }
            }
            AtomicExprKind::Number(number) => u32::try_from(*number)
                .ok()
                .and_then(|as_u32| Word::from_sign_u32(Sign::Plus, as_u32))
                .ok_or_else(|| {
                    self.err_number_out_of_range(atomic_expr, *number)
                }),
        }
    }

    /// Evaluate an expression.
    fn eval_expr(&mut self, expr: &Expr) -> Result<Word, ()> {
        let mut error = false;
        let mut value = self
            .eval_atomic_expr(expr.head())
            .inspect_err(|_| error = true)
            .unwrap_or_default();

        if expr.sign() == Some(Sign::Minus) {
            value = -value;
        }

        for (bin_op, atomic_expr) in expr.tail() {
            let rhs = self
                .eval_atomic_expr(atomic_expr)
                .inspect_err(|_| error = true)
                .unwrap_or_default();

            value = match bin_op {
                ExprBinOp::Add => value.overflowing_add(rhs).0,
                ExprBinOp::Sub => value.overflowing_sub(rhs).0,
                // Get the low word of mul.
                ExprBinOp::Mul => value.overflowing_mul(rhs).0,
                ExprBinOp::Div => {
                    // Ensure the numerator has `value`'s sign.
                    let num_hi = Word::from_sign_u32(value.sign(), 0).unwrap();

                    crate::num::machine::div(num_hi, value, rhs).0
                }
                ExprBinOp::HighDiv => {
                    crate::num::machine::div(value, Word::POS_ZERO, rhs).0
                }
                ExprBinOp::Colon => {
                    // value:rhs = 8 * value + rhs
                    word!(8).overflowing_mul(value).0.overflowing_add(rhs).0
                }
            }
        }

        if error { Err(()) } else { Ok(value) }
    }

    /// Evaluate a W-value.
    fn eval_w_value(&mut self, w_value: &WValue) -> Result<Word, ()> {
        let mut error = false;
        let mut value = Word::POS_ZERO;

        for (expr, f_part) in w_value.parts() {
            let expr_value = self
                .eval_expr(expr)
                .inspect_err(|_| error = true)
                .unwrap_or_default();

            value = match f_part.kind() {
                FPartKind::Empty => expr_value,
                FPartKind::Expr(f_part_expr) => {
                    let f_part_val = self
                        .eval_expr(f_part_expr)
                        .inspect_err(|_| error = true)
                        .unwrap_or_default();

                    Byte::try_from(f_part_val)
                        .ok()
                        .and_then(FieldSpec::from_byte)
                        .map(|spec| value.with_store(expr_value, spec))
                        .unwrap_or_else(|| {
                            self.err_field_out_of_range(f_part, f_part_val);
                            Word::POS_ZERO
                        })
                }
            }
        }

        if error { Err(()) } else { Ok(value) }
    }

    /// Evaluate an A-part.
    fn eval_a_part(&mut self, a_part: &APart) -> Result<Word, ()> {
        match a_part.kind() {
            APartKind::Expr(expr) => self.eval_expr(expr),
            _ => Ok(Word::POS_ZERO),
        }
    }

    /// Evaluate an I-part.
    fn eval_i_part(&mut self, i_part: &IPart) -> Result<Word, ()> {
        match i_part.kind() {
            IPartKind::Empty => Ok(Word::POS_ZERO),
            IPartKind::Expr(expr) => self.eval_expr(expr),
        }
    }

    /// Evaluate an F-part.
    fn eval_f_part(&mut self, f_part: &FPart) -> Result<Word, ()> {
        match f_part.kind() {
            FPartKind::Empty => Ok(Word::POS_ZERO),
            FPartKind::Expr(expr) => self.eval_expr(expr),
        }
    }

    /// Add the value into data at the current location counter. Also stores
    /// source map info and increments location.
    fn push_data(&mut self, line: &Line, value: Word) -> Result<DataInfo, ()> {
        let address = MemoryAddress::try_from(self.location_counter)
            .map_err(|_| self.err_location_is_invalid_address(line))?;

        match self.source_map.entry(address) {
            Entry::Vacant(vacant) => vacant.insert(line.span()),
            Entry::Occupied(_) => {
                self.err_multiple_data_at_address(line, address);
                return Err(());
            }
        };

        // Location counter increment is always a valid location counter since
        // it is currently a valid memory address as checked above.
        self.location_counter = self.location_counter.increment().unwrap();

        if self.current_section_next_address() == Some(address) {
            self.sections.last_mut().unwrap().data.push(value);
        } else {
            self.sections.push(ProgramSection { address, data: vec![value] });
        }

        let section_index = self.sections.len() - 1;
        let section_offset = self.sections.last_mut().unwrap().data.len() - 1;

        Ok(DataInfo {
            address,
            pos: DataPos { section_index, section_offset },
        })
    }

    /// Gets the next memory address represented by the current section if
    /// it a section exists and the next address is valid.
    fn current_section_next_address(&self) -> Option<MemoryAddress> {
        if let Some(section) = self.sections.last() {
            section
                .data
                .len()
                .checked_add(section.address.to_usize())
                .and_then(|v| MemoryAddress::try_from(v).ok())
        } else {
            None
        }
    }

    /// Define a symbol. Fixes existing future references.
    fn define_symbol(&mut self, loc: &Loc, value: Word) {
        let symbol = loc.symbol();
        // Make symbol info for insertion into table.
        let make_info = || ActiveSymbolInfo {
            definition: loc.span(),
            value,
            references: Vec::new(),
        };

        // Get reference to the inserted active symbol info.
        let active = match self.active_symbols.entry(symbol) {
            Entry::Vacant(vacant) => vacant.insert(make_info()),
            Entry::Occupied(mut occupied) => {
                // Cannot redefine non local symbols.
                if let Symbol::NonLocal(name) = symbol {
                    let definition = occupied.get().definition;
                    return self.err_redefined_symbol(loc, name, definition);
                }

                // Store old symbol information while inserting new.
                self.inactive_symbols.push(
                    occupied.insert(make_info()).into_debug_info(symbol),
                );
                occupied.into_mut()
            }
        };

        // Fixup future references and remove their entry in the insert table.
        if let Some(inserts) = self.future_ref_inserts.remove(&symbol) {
            active.references.reserve(inserts.len());

            for insert in inserts {
                active.references.push(insert.reference);

                let target = &mut self.sections[insert.pos.section_index].data
                    [insert.pos.section_offset];

                *target = target.with_address(value);
            }
        }
    }

    /// Define the symbol in `maybe_def` to be `value` if it exists.
    fn maybe_define_symbol(&mut self, maybe_loc: Option<&Loc>, value: Word) {
        maybe_loc.inspect(|loc| self.define_symbol(loc, value));
    }
}

pub fn assemble(
    ast: &Ast,
    source: &str,
    source_path: Option<PathBuf>,
) -> Result<Program, Vec<AssemblyError>> {
    Assembler::new(ast, source, source_path).assemble()
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::char::Char;
    use crate::symbol::{SymbolIndex, SymbolName};

    use super::*;

    fn make_nonlocal(src: &str) -> Symbol {
        Symbol::NonLocal(SymbolName::from_str(src).unwrap())
    }

    fn make_local(index: usize) -> Symbol {
        Symbol::Local(SymbolIndex::from_usize(index).unwrap())
    }

    fn make_bytes(arr: [u8; 5]) -> [Byte; 5] {
        arr.map(|b| Byte::try_from(b).unwrap())
    }

    fn make_word(value: i32) -> Word {
        Word::from_sign_u32(
            if value >= 0 { Sign::Plus } else { Sign::Minus },
            value.unsigned_abs(),
        )
        .unwrap()
    }

    #[test]
    fn assemble_err_no_entry_point() {
        let src = " ADD 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::empty(src.len()),
                kind: AssemblyErrorKind::NoEntryPoint
            }])
        );
    }

    #[test]
    fn assemble_err_code_after_end() {
        let src = " ADD 0\n ADD 0\n END 0\n ADD 0\n ADD 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(21..34),
                kind: AssemblyErrorKind::CodeAfterEnd
            }])
        );
    }

    #[test]
    fn assemble_err_invalid_index() {
        let src = " ADD 0,7\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let value = make_word(7);

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(6..8),
                kind: AssemblyErrorKind::InvalidIndex { value }
            }])
        );
    }

    #[test]
    fn assemble_err_invalid_field() {
        for (src, value, span) in [
            (" ADD 0(999999)\n END 0", 999999, Span::from(6..14)),
            (" ADD 0(7)\n END 0", 7, Span::from(6..9)),
        ] {
            let ast = Ast::from_str(src).unwrap();
            let value = make_word(value);

            assert_eq!(
                assemble(&ast, src, None),
                Err(vec![AssemblyError {
                    span,
                    kind: AssemblyErrorKind::InvalidField {
                        op: Op::ADD,
                        value
                    }
                }])
            );
        }
    }

    #[test]
    fn assemble_err_undefined_symbol() {
        let src = " ADD 0+L\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(7..8),
                kind: AssemblyErrorKind::UndefinedSymbol {
                    symbol: make_nonlocal("L")
                }
            }])
        );
    }

    #[test]
    fn assemble_err_number_out_of_range() {
        let src = " ADD 9999999999\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(5..15),
                kind: AssemblyErrorKind::NumberOutOfRange {
                    number: 9999999999
                }
            }])
        );
    }

    #[test]
    fn assemble_err_field_out_of_range() {
        let src = " ORIG 0(7)\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(7..10),
                kind: AssemblyErrorKind::FieldOutOfRange {
                    value: make_word(7)
                }
            }])
        );
    }

    #[test]
    fn assemble_err_redefined_symbol() {
        let src = "L EQU 0\nL EQU 1\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(8..9),
                kind: AssemblyErrorKind::RedefinedNonLocalSymbol {
                    definition: Span::from(0..1),
                    name: SymbolName::try_from("L").unwrap(),
                }
            }])
        );
    }

    #[test]
    fn assemble_err_multiple_data_at_address() {
        let src = " ORIG 500\n ADD 0\n ORIG 500\n ADD 0\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(27..33),
                kind: AssemblyErrorKind::MultipleDataAtAddress {
                    address: MemoryAddress::try_from(500).unwrap()
                }
            }])
        );
    }

    #[test]
    fn assemble_err_invalid_location_counter() {
        let src = " ORIG 100000\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(6..12),
                kind: AssemblyErrorKind::InvalidLocation {
                    value: make_word(100000)
                }
            }])
        )
    }

    #[test]
    fn assemble_err_invalid_entry_point() {
        let src = " END 4001";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(5..9),
                kind: AssemblyErrorKind::InvalidEntryPoint {
                    value: make_word(4001)
                }
            },])
        )
    }

    #[test]
    fn assemble_err_location_counter_is_invalid_address() {
        let src = " ORIG 4001\n CON 0\n END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(11..17),
                kind: AssemblyErrorKind::LocationIsInvalidAddress {
                    location_counter: LocationCounter::try_from(4001).unwrap()
                }
            }])
        );
    }

    #[test]
    fn assemble_err_location_counter_overflow() {
        let src = " ADD L\n ORIG 4095\nX END 0";
        let ast = Ast::from_str(src).unwrap();

        assert_eq!(
            assemble(&ast, src, None),
            Err(vec![AssemblyError {
                span: Span::from(18..25),
                kind: AssemblyErrorKind::LocationCounterOverflow
            }])
        );
    }

    #[test]
    fn assemble_ok_mix_parts() {
        // DIV has opcode 4.
        let src = " DIV -1,2(3)\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let bytes = make_bytes([0, 1, 2, 3, 4]);
        let word = Word::from_sign_bytes(Sign::Minus, bytes);

        assert_eq!(
            program.sections,
            vec![ProgramSection {
                address: MemoryAddress::MIN,
                data: vec![word]
            }]
        );
    }

    #[test]
    fn assemble_ok_mix_literal_constant() {
        // MOVE has opcode 7.
        let src = " MOVE =123=,3(4)\n NOP 0\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let bytes0 = make_bytes([0, 2, 3, 4, 7]);
        let word0 = Word::from_sign_bytes(Sign::Plus, bytes0);
        let word1 = Word::POS_ZERO;
        let word2 = make_word(123);

        assert_eq!(
            program.sections,
            vec![ProgramSection {
                address: MemoryAddress::MIN,
                data: vec![word0, word1, word2]
            }]
        );

        assert_eq!(
            program.debug_info.literal_constants,
            vec![LiteralConstantDebugInfo {
                address: MemoryAddress::try_from(2).unwrap(),
                definition: Span::from(6..11),
                value: make_word(123)
            }]
        );
    }

    #[test]
    fn assemble_ok_mix_future_ref_defined() {
        // MOVE has opcode 7.
        let src = " MOVE L,3(4)\nL EQU 2\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let bytes0 = make_bytes([0, 2, 3, 4, 7]);
        let word0 = Word::from_sign_bytes(Sign::Plus, bytes0);

        assert_eq!(
            program.sections,
            vec![ProgramSection {
                address: MemoryAddress::MIN,
                data: vec![word0]
            }]
        );

        assert_eq!(
            program.debug_info.symbols,
            vec![SymbolDebugInfo {
                definition: Some(Span::from(13..14)),
                references: vec![Span::from(6..7)],
                symbol: make_nonlocal("L"),
                value: make_word(2)
            }]
        );
    }

    #[test]
    fn assemble_ok_mix_future_ref_undefined() {
        // MOVE has opcode 7.
        for (src, definition) in [
            (" MOVE L,3(4)\nL CON 0\n END 0", Some(Span::from(13..14))),
            (" MOVE L,3(4)\n END 0", None),
        ] {
            let ast = Ast::from_str(src).unwrap();
            let program = assemble(&ast, src, None).unwrap();
            let bytes0 = make_bytes([0, 1, 3, 4, 7]);
            let word0 = Word::from_sign_bytes(Sign::Plus, bytes0);

            assert_eq!(
                program.sections,
                vec![ProgramSection {
                    address: MemoryAddress::MIN,
                    data: vec![word0, Word::POS_ZERO]
                }]
            );

            assert_eq!(
                program.debug_info.symbols,
                vec![SymbolDebugInfo {
                    definition,
                    references: vec![Span::from(6..7)],
                    symbol: make_nonlocal("L"),
                    value: make_word(1),
                }]
            );
        }
    }

    #[test]
    fn assemble_ok_equ() {
        let src = "L EQU 123\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();

        assert_eq!(
            program.debug_info.symbols,
            vec![SymbolDebugInfo {
                definition: Some(Span::from(0..1)),
                references: vec![],
                symbol: make_nonlocal("L"),
                value: make_word(123)
            }]
        );
    }

    #[test]
    fn assemble_ok_orig() {
        let src = "
            ORIG 500
            ORIG 1000
            CON 1
            ORIG 2000
            CON 2
            CON 3
            ORIG 2002
            CON 4
            ORIG 3000
            END 0
        ";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let [w1, w2, w3, w4] = [1, 2, 3, 4].map(|v| make_word(v));
        let [m1000, m2000] =
            [1000, 2000].map(|v| MemoryAddress::try_from(v).unwrap());

        assert_eq!(
            program.sections,
            vec![
                ProgramSection { address: m1000, data: vec![w1] },
                ProgramSection { address: m2000, data: vec![w2, w3, w4] }
            ]
        );
    }

    #[test]
    fn assemble_ok_con() {
        let src = " ORIG 1000\n CON 123\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let address = MemoryAddress::try_from(1000).unwrap();
        let value = make_word(123);

        assert_eq!(
            program.sections,
            vec![ProgramSection { address, data: vec![value] }]
        );

        assert_eq!(
            program.debug_info.constants,
            vec![ConstantDebugInfo {
                definition: Span::from(16..19),
                address,
                value
            }]
        );
    }

    #[test]
    fn assemble_ok_alf() {
        let src = " ORIG 1000\n ALF \"ABCDE\"\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let address = MemoryAddress::try_from(1000).unwrap();
        let bytes = make_bytes([1, 2, 3, 4, 5]);
        let value = Word::from_sign_bytes(Sign::Plus, bytes);
        let chars = bytes.map(|b| Char::try_from(b).unwrap());

        assert_eq!(
            program.sections,
            vec![ProgramSection { address, data: vec![value] }]
        );

        assert_eq!(
            program.debug_info.strings,
            vec![AlfStringDebugInfo {
                address,
                definition: Span::from(16..23),
                chars
            }]
        );
    }

    #[test]
    fn assemble_ok_end_entry_point_4_5() {
        // 64440 = 0b1111_101110_111000
        // 3000 = 0b101110_111000
        let src = " END -64440";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let entry_point = MemoryAddress::try_from(3000).unwrap();

        assert_eq!(program.entry_point, entry_point);
    }

    #[test]
    fn assemble_ok_end_loc_def_after_inserts() {
        for (src, value) in [
            (" ADD L1\nL END 0", 2),
            (" ADD L1\n ADD L1\nL END 0", 3),
            (" ADD L1\n ADD L2\nL END 0", 4),
            (" ADD =0=\nL END 0", 2),
            (" ADD =0=\n ADD =0=\nL END 0", 4),
            (" ADD L1\n ADD =0=\nL END 0", 4),
            (" ADD L1\n ADD L\nL END 0", 3),
        ] {
            let ast = Ast::from_str(src).unwrap();
            let program = assemble(&ast, src, None).unwrap();
            let symbols = &program.debug_info.symbols;
            let mut l_value = symbols
                .iter()
                .filter(|info| info.symbol == make_nonlocal("L"))
                .map(|info| info.value);

            assert_eq!(l_value.clone().count(), 1);
            assert_eq!(l_value.next(), Some(make_word(value)));
        }
    }

    #[test]
    fn assemble_ok_redefine_local_symbols() {
        let src = "1H CON 0\n ADD 1F\n1H CON 1B\n END 0";
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, None).unwrap();
        let w2 = make_word(2);

        assert_eq!(
            program.sections,
            vec![ProgramSection {
                address: MemoryAddress::MIN,
                data: vec![
                    Word::POS_ZERO,
                    Word::POS_ZERO
                        .with_address(make_word(2))
                        .with_opcode(OpCode::Add.to_byte().into()),
                    Word::POS_ZERO,
                ]
            }]
        );

        assert_eq!(
            program.debug_info.symbols,
            vec![
                SymbolDebugInfo {
                    definition: Some(Span::from(0..2)),
                    symbol: make_local(1),
                    value: Word::POS_ZERO,
                    references: vec![Span::from(24..26)]
                },
                SymbolDebugInfo {
                    definition: Some(Span::from(17..19)),
                    symbol: make_local(1),
                    value: w2,
                    references: vec![Span::from(14..16)]
                }
            ]
        );
    }

    #[test]
    fn assemble_ok_eval() {
        for (expr, value) in [
            ("1+2", 3),
            ("1-2", -1),
            ("2*3", 6),
            ("100/6", 16),
            ("-100/6", -16),
            ("1//3", 357913941),
            ("1:3", 11),
            ("-1+5*20/6", 13),
            ("1", 1),
            ("0,1", 1),
            ("0,1(0:5)", 1),
            ("-1,0(1:3)", -1),
        ] {
            let src = format!("L EQU {expr}\n END 0");
            let ast = Ast::from_str(&src).unwrap();
            let program = assemble(&ast, &src, None).unwrap();
            let value = make_word(value);
            let symbol_values: Vec<_> = program
                .debug_info
                .symbols
                .iter()
                .map(|info| info.value)
                .collect();

            assert_eq!(symbol_values, vec![value]);
        }
    }

    #[test]
    fn assemble_ok_location_literal_debug_info() {
        let src = " ORIG 2000\n CON *\n END 0";
        let ast = Ast::from_str(&src).unwrap();
        let program = assemble(&ast, &src, None).unwrap();

        dbg!(ast);

        assert_eq!(
            program.debug_info.location_literals,
            vec![LocationLiteralDebugInfo {
                span: Span::new(16, 17),
                value: LocationCounter::try_from(2000).unwrap()
            }]
        )
    }
}
