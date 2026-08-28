use mixlib::asm::{Program, ProgramDebugInfo};
use mixlib::char::Char;
use mixlib::num::{MemoryAddress, Word};
use mixlib::source::BytePos;
use mixlib::symbol::{Symbol, SymbolName};

use std::collections::HashMap;
use std::fmt;

struct LineInfo {
    newlines: Vec<usize>,
}

impl LineInfo {
    fn new(src: &str) -> Self {
        assert!(BytePos::try_from(src.len()).is_ok());

        let mut newlines = Vec::new();

        for (index, c) in src.bytes().enumerate() {
            if c == b'\n' {
                newlines.push(index);
            }
        }

        Self { newlines }
    }

    /// 1-indexed line
    fn line_of(&self, pos: usize) -> usize {
        match self.newlines.binary_search(&pos) {
            Ok(index) => index + 1,
            Err(index) => index + 1,
        }
    }
}

struct MemoryEntry {
    address: MemoryAddress,
    line: usize,
    word: Word,
    chars: Option<[Char; 5]>,
}

struct SymbolEntry {
    name: SymbolName,
    value: Word,
}

pub struct Summary {
    line_col_width: usize,
    symbol_table: Vec<SymbolEntry>,
    memory_table: Vec<MemoryEntry>,
}

impl Summary {
    pub fn new(
        src: &str,
        program: &Program,
        program_debug_info: &ProgramDebugInfo,
    ) -> Self {
        let symbol_table =
            Vec::from_iter(program_debug_info.symbols().iter().filter_map(
                |info| match info.symbol() {
                    Symbol::NonLocal(name) => {
                        Some(SymbolEntry { name, value: info.value() })
                    }
                    _ => None,
                },
            ));

        let line_info = LineInfo::new(src);
        let string_map = HashMap::<MemoryAddress, [Char; 5]>::from_iter(
            program_debug_info
                .strings()
                .iter()
                .map(|info| (info.address(), info.chars())),
        );

        let mut memory_table = Vec::new();
        let mut max_line = 0;

        for section in program.sections() {
            let min_address = section.address().to_u16();

            for (offset, &word) in section.data().iter().enumerate() {
                let address =
                    MemoryAddress::try_from(min_address + offset as u16)
                        .unwrap();

                let chars = string_map.get(&address).copied();
                let line = line_info.line_of(
                    program_debug_info
                        .source_map()
                        .get(&address)
                        .unwrap()
                        .start()
                        .to_usize(),
                );

                max_line = max_line.max(line);
                memory_table.push(MemoryEntry { address, line, word, chars });
            }
        }

        let max_line_digits = max_line.checked_ilog10().unwrap_or(0) + 1;
        let line_col_width = 4.max(max_line_digits as usize);

        memory_table.sort_by_key(|entry| entry.address);

        Self { line_col_width, memory_table, symbol_table }
    }
}

impl fmt::Display for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("\n** Symbol Table\n")?;

        for entry in &self.symbol_table {
            f.write_fmt(format_args!(
                "{: <11} := {}\n",
                entry.name, entry.value
            ))?;
        }

        f.write_str("\n** Memory\n")?;
        f.write_fmt(format_args!(
            "{:-<55}\n{: <lcw$}    Address   Word                Repr\n{:-<55}\n",
            "",
            "Line",
            "",
            lcw = self.line_col_width
        ))?;

        for entry in &self.memory_table {
            let (sign, [b1, b2, b3, b4, b5]) = entry.word.to_sign_bytes();

            f.write_fmt(format_args!(
                "{:0lcw$}    {:04}      {} {:02} {:02} {:02} {:02} {:02}    ",
                entry.line,
                entry.address,
                sign,
                b1,
                b2,
                b3,
                b4,
                b5,
                lcw = self.line_col_width
            ))?;

            if let Some(chars) = entry.chars {
                f.write_fmt(format_args!(
                    "ALF \"{}{}{}{}{}\"\n",
                    chars[0], chars[1], chars[2], chars[3], chars[4],
                ))?;
            } else {
                f.write_fmt(format_args!("CON {}\n", entry.word))?;
            }
        }

        Ok(())
    }
}
