use std::error;
use std::fmt;

use crate::asm::{Op, OpCode};
use crate::num::{Byte, Short, Word};

/// Enum storing the kind of error when converting to an [`Instruction`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InstructionTryFromErrorKind {
    /// The field value is invalid.
    InvalidField,
    /// The index value is invalid.
    ///
    /// In particular, indexes greater than `6` are not valid since indexes are
    /// always used to identify an index register in a MIX machine.
    InvalidIndex,
}

use InstructionTryFromErrorKind::*;

/// An error that can be returned when converting to an [`Instruction`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstructionTryFromError {
    kind: InstructionTryFromErrorKind,
}

impl InstructionTryFromError {
    /// Get the kind of instruction conversion error.
    pub const fn kind(&self) -> &InstructionTryFromErrorKind {
        &self.kind
    }
}

impl error::Error for InstructionTryFromError {}

impl fmt::Display for InstructionTryFromError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self.kind {
            InvalidField => "invalid field",
            InvalidIndex => "invalid index",
        })
    }
}

/// A MIX instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Instruction {
    op: Op,
    field: Byte,
    index: Byte,
    address: Short,
}

impl Instruction {
    /// Returns the operation value of the instruction.
    pub const fn op(&self) -> Op {
        self.op
    }

    /// Returns the field value of the instruction.
    pub const fn field(&self) -> Byte {
        self.field
    }

    /// Returns the address value of the instruction.
    pub const fn address(&self) -> Short {
        self.address
    }

    /// Returns the index value of the instruction.
    pub const fn index(&self) -> Byte {
        self.index
    }
}

impl From<Instruction> for Word {
    fn from(value: Instruction) -> Self {
        let (sign, [a1, a2]) = value.address.to_sign_bytes();

        Word::from_sign_bytes(
            sign,
            [a1, a2, value.index, value.field, Byte::from(value.op.opcode())],
        )
    }
}

impl TryFrom<Word> for Instruction {
    type Error = InstructionTryFromError;

    fn try_from(value: Word) -> Result<Self, Self::Error> {
        let (sign, [a1, a2, index, field, opcode]) = value.to_sign_bytes();

        if index.to_u8() > 6 {
            return Err(InstructionTryFromError { kind: InvalidIndex });
        }

        let address = Short::from_sign_bytes(sign, [a1, a2]);

        // Note that all opcode values exist, so only the field can be
        // incorrect. That is, some opcodes are overloaded by field.
        let op = Op::from_opcode_and_field(OpCode::from(opcode), field)
            .ok_or_else(|| InstructionTryFromError { kind: InvalidField })?;

        Ok(Instruction { op, address, index, field })
    }
}
