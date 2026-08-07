use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};

use crate::bin::*;
use crate::char::Char;
use crate::num::{MemoryAddress, Word};
use crate::source::Span;
use crate::symbol::Symbol;

/// A complete MIX program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub(super) entry_point: MemoryAddress,
    pub(super) sections: Vec<ProgramSection>,
    pub(super) debug_info: ProgramDebugInfo,
}

impl Program {
    /// The entry point of the program.
    pub fn entry_point(&self) -> MemoryAddress {
        self.entry_point
    }

    /// All sections the program loads into memory
    pub fn sections(&self) -> &[ProgramSection] {
        &self.sections
    }

    /// The program's debug info, if any.
    pub fn debug_info(&self) -> &ProgramDebugInfo {
        &self.debug_info
    }

    pub fn encode<W: io::Write>(&mut self, w: W) -> io::Result<()> {
        <Self as Encode>::encode(self, w)
    }

    pub fn decode<R: io::Read>(r: R) -> io::Result<Program> {
        <Self as Decode>::decode(r)
    }
}

impl Encode for Program {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.entry_point.encode(&mut w)?;
        self.sections.encode(&mut w)?;
        self.debug_info.encode(&mut w)
    }
}

impl Decode for Program {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(Program {
            entry_point: Decode::decode(&mut r)?,
            sections: Decode::decode(&mut r)?,
            debug_info: Decode::decode(&mut r)?,
        })
    }
}

/// A single section of program data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramSection {
    pub(super) address: MemoryAddress,
    pub(super) data: Vec<Word>,
}

impl ProgramSection {
    /// The base address of this section.
    pub fn address(&self) -> MemoryAddress {
        self.address
    }

    /// The data to be loaded at [`address`], in order.
    ///
    /// [`address`]: Self::address
    pub fn data(&self) -> &[Word] {
        &self.data
    }
}

impl Encode for ProgramSection {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.address.encode(&mut w)?;
        self.data.encode(&mut w)
    }
}

impl Decode for ProgramSection {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(ProgramSection {
            address: Decode::decode(&mut r)?,
            data: Decode::decode(&mut r)?,
        })
    }
}

/// Debug info of a program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProgramDebugInfo {
    pub(super) source_map: HashMap<MemoryAddress, Span>,
    pub(super) source_path: Option<PathBuf>,
    pub(super) source_hash: u64,
    pub(super) symbols: Vec<SymbolDebugInfo>,
    pub(super) constants: Vec<ConstantDebugInfo>,
    pub(super) literal_constants: Vec<LiteralConstantDebugInfo>,
    pub(super) strings: Vec<AlfStringDebugInfo>,
}

impl ProgramDebugInfo {
    /// A map from memory addresses to the source lines.
    pub fn source_map(&self) -> &HashMap<MemoryAddress, Span> {
        &self.source_map
    }

    /// The path of the source code. This is optional since the code may have
    /// not been compiled from a file.
    pub fn source_path(&self) -> Option<&Path> {
        self.source_path.as_deref()
    }

    /// A hash of the source code. This is used heuristically to determine
    /// equality in place of storing the entire source code. If the source of
    /// some file at [`source_path`] hashes to the same as [`source_hash`],
    /// then we assume that this the file has not been changed.
    ///
    /// [`source_path`]: Self::source_path
    /// [`source_hash`]: Self::source_hash
    pub fn source_hash(&self) -> u64 {
        self.source_hash
    }

    /// List of symbol debug info.
    pub fn symbols(&self) -> &[SymbolDebugInfo] {
        &self.symbols
    }

    /// List of all constants defined by the `CON` operation.
    pub fn constants(&self) -> &[ConstantDebugInfo] {
        &self.constants
    }

    /// List of all literal constants used.
    pub fn literal_constants(&self) -> &[LiteralConstantDebugInfo] {
        &self.literal_constants
    }
    /// List of all strings defined with the `ALF` operation.
    pub fn strings(&self) -> &[AlfStringDebugInfo] {
        &self.strings
    }
}

impl Encode for ProgramDebugInfo {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.source_map.encode(&mut w)?;
        self.source_path.encode(&mut w)?;
        self.source_hash.encode(&mut w)?;
        self.symbols.encode(&mut w)?;
        self.constants.encode(&mut w)?;
        self.literal_constants.encode(&mut w)?;
        self.strings.encode(&mut w)
    }
}

impl Decode for ProgramDebugInfo {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(ProgramDebugInfo {
            source_map: Decode::decode(&mut r)?,
            source_path: Decode::decode(&mut r)?,
            source_hash: Decode::decode(&mut r)?,
            symbols: Decode::decode(&mut r)?,
            constants: Decode::decode(&mut r)?,
            literal_constants: Decode::decode(&mut r)?,
            strings: Decode::decode(&mut r)?,
        })
    }
}

/// Symbol debug info.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymbolDebugInfo {
    pub(super) symbol: Symbol,
    pub(super) definition: Option<Span>,
    pub(super) references: Vec<Span>,
    pub(super) value: Word,
}

impl SymbolDebugInfo {
    /// The symbol value.
    pub fn symbol(&self) -> Symbol {
        self.symbol
    }

    /// The definition of the symbol. Since future references can be left
    /// undefined, this is optional.
    pub fn definition(&self) -> Option<Span> {
        self.definition
    }

    /// References to the symbol.
    pub fn references(&self) -> &[Span] {
        &self.references
    }

    /// Value assumed by the symbol.
    pub fn value(&self) -> Word {
        self.value
    }
}

impl Encode for SymbolDebugInfo {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.symbol.encode(&mut w)?;
        self.definition.encode(&mut w)?;
        self.references.encode(&mut w)?;
        self.value.encode(&mut w)
    }
}

impl Decode for SymbolDebugInfo {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(SymbolDebugInfo {
            symbol: Decode::decode(&mut r)?,
            definition: Decode::decode(&mut r)?,
            references: Decode::decode(&mut r)?,
            value: Decode::decode(&mut r)?,
        })
    }
}

/// Debug info of a constant defined by the `CON` operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstantDebugInfo {
    pub(super) definition: Span,
    pub(super) address: MemoryAddress,
    pub(super) value: Word,
}

impl ConstantDebugInfo {
    /// The span of the [`WValue`] defining this constant.
    pub fn definition(&self) -> Span {
        self.definition
    }

    /// The memory address this constant is loaded into.
    pub fn address(&self) -> MemoryAddress {
        self.address
    }

    /// The computed value of the constant.
    pub fn value(&self) -> Word {
        self.value
    }
}

impl Encode for ConstantDebugInfo {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.definition.encode(&mut w)?;
        self.address.encode(&mut w)?;
        self.value.encode(&mut w)
    }
}

impl Decode for ConstantDebugInfo {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(ConstantDebugInfo {
            definition: Decode::decode(&mut r)?,
            address: Decode::decode(&mut r)?,
            value: Decode::decode(&mut r)?,
        })
    }
}

/// Debug info of a literal constant defined by the equals sign syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralConstantDebugInfo {
    pub(super) definition: Span,
    pub(super) address: MemoryAddress,
    pub(super) value: Word,
}

impl LiteralConstantDebugInfo {
    /// The span of the [`LiteralConstant`] defining this literal constant.
    pub fn definition(&self) -> Span {
        self.definition
    }

    /// The memory address the constant is loaded into.
    pub fn address(&self) -> MemoryAddress {
        self.address
    }

    /// The computed value of the literal constant.
    pub fn value(&self) -> Word {
        self.value
    }
}

impl Encode for LiteralConstantDebugInfo {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.definition.encode(&mut w)?;
        self.address.encode(&mut w)?;
        self.value.encode(&mut w)
    }
}

impl Decode for LiteralConstantDebugInfo {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(LiteralConstantDebugInfo {
            definition: Decode::decode(&mut r)?,
            address: Decode::decode(&mut r)?,
            value: Decode::decode(&mut r)?,
        })
    }
}

/// Debug info of a string defined by the `ALF` operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlfStringDebugInfo {
    pub(super) definition: Span,
    pub(super) address: MemoryAddress,
    pub(super) chars: [Char; 5],
}

impl AlfStringDebugInfo {
    /// Span of the [`AlfString`] defining this.
    pub fn definition(&self) -> Span {
        self.definition
    }

    /// The memory address the string is loaded into.
    pub fn address(&self) -> MemoryAddress {
        self.address
    }

    /// The string's characters.
    pub fn chars(&self) -> [Char; 5] {
        self.chars
    }
}

impl Encode for AlfStringDebugInfo {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.definition.encode(&mut w)?;
        self.address.encode(&mut w)?;
        self.chars.encode(&mut w)
    }
}

impl Decode for AlfStringDebugInfo {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(AlfStringDebugInfo {
            definition: Decode::decode(&mut r)?,
            address: Decode::decode(&mut r)?,
            chars: Decode::decode(&mut r)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::asm::assemble;
    use crate::ast::Ast;

    use super::*;

    #[test]
    fn encode_round_trip_primes() {
        let path =
            PathBuf::from("src/asm/primes.mixal").canonicalize().unwrap();
        let src = include_str!("primes.mixal");
        let ast = Ast::from_str(src).unwrap();
        let program = assemble(&ast, src, Some(path)).unwrap();

        let mut buf = Vec::new();
        program.encode(&mut buf).unwrap();

        let decoded = Program::decode(buf.as_slice()).unwrap();
        assert_eq!(program, decoded);
    }
}
