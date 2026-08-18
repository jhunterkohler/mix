use std::error;
use std::fmt;
use std::mem;

use crate::asm::Op;
use crate::num::Sign;
use crate::num::{Byte, Short, Word};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidInstructionIndexError(());

impl fmt::Display for InvalidInstructionIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid instruction index")
    }
}

impl error::Error for InvalidInstructionIndexError {}

#[repr(u8)]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default,
)]
pub enum InstructionIndex {
    #[default]
    None = 0,
    I1 = 1,
    I2 = 2,
    I3 = 3,
    I4 = 4,
    I5 = 5,
    I6 = 6,
}

impl InstructionIndex {
    pub const fn to_byte(self) -> Byte {
        unsafe { Byte::from_u8_unchecked(self as u8) }
    }

    pub const fn from_byte(value: Byte) -> Option<Self> {
        if value.to_u8() <= 6 {
            Some(unsafe { mem::transmute(value.to_u8()) })
        } else {
            None
        }
    }
}

impl From<InstructionIndex> for Byte {
    fn from(value: InstructionIndex) -> Self {
        value.to_byte()
    }
}

impl TryFrom<Byte> for InstructionIndex {
    type Error = InvalidInstructionIndexError;

    fn try_from(value: Byte) -> Result<Self, Self::Error> {
        Self::from_byte(value).ok_or(InvalidInstructionIndexError(()))
    }
}

/// Enum storing the kind of error when converting to an [`Instruction`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvalidInstructionErrorKind {
    /// The field value is invalid.
    InvalidField,
    /// The index value is invalid.
    ///
    /// In particular, indexes greater than `6` are not valid since indexes are
    /// always used to identify an index register in a MIX machine.
    InvalidIndex,
}

/// An error that can be returned when converting to an [`Instruction`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidInstructionError {
    kind: InvalidInstructionErrorKind,
}

impl InvalidInstructionError {
    /// Get the kind of instruction conversion error.
    pub const fn kind(&self) -> &InvalidInstructionErrorKind {
        &self.kind
    }
}

impl fmt::Display for InvalidInstructionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self.kind {
            InvalidInstructionErrorKind::InvalidField => "invalid field",
            InvalidInstructionErrorKind::InvalidIndex => "invalid index",
        })
    }
}

impl error::Error for InvalidInstructionError {}

/// A MIX instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Instruction {
    op: Op,
    field: Byte,
    index: InstructionIndex,
    address: Short,
}

impl Instruction {
    pub const fn sign(&self) -> Sign {
        self.address.sign()
    }

    pub const fn op(&self) -> Op {
        self.op
    }

    pub const fn index(&self) -> InstructionIndex {
        self.index
    }

    pub const fn field(&self) -> Byte {
        self.field
    }

    pub const fn address(&self) -> Short {
        self.address
    }
}

impl From<Instruction> for Word {
    fn from(value: Instruction) -> Self {
        let (sign, [a1, a2]) = value.address.to_sign_bytes();
        let bytes = [
            a1,
            a2,
            value.index.to_byte(),
            value.field,
            value.op.opcode().to_byte(),
        ];

        Word::from_sign_bytes(sign, bytes)
    }
}

impl TryFrom<Word> for Instruction {
    type Error = InvalidInstructionError;

    fn try_from(value: Word) -> Result<Self, Self::Error> {
        let (sign, [a1, a2, index, field, opcode]) = value.to_sign_bytes();

        let index = InstructionIndex::try_from(index).map_err(|_| {
            InvalidInstructionError {
                kind: InvalidInstructionErrorKind::InvalidIndex,
            }
        })?;

        let address = Short::from_sign_bytes(sign, [a1, a2]);
        let op = Op::from_opcode_and_field(opcode.into(), field).ok_or(
            InvalidInstructionError {
                kind: InvalidInstructionErrorKind::InvalidField,
            },
        )?;

        Ok(Instruction { op, index, address, field })
    }
}
