use std::error;
use std::fmt;
use std::mem;

use crate::num::LocationCounter;
use crate::num::{Short, Word};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryFromRegError(());

impl fmt::Display for TryFromRegError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid register conversion")
    }
}

impl error::Error for TryFromRegError {}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IndexReg {
    I1 = Reg::I1 as u8,
    I2 = Reg::I2 as u8,
    I3 = Reg::I3 as u8,
    I4 = Reg::I4 as u8,
    I5 = Reg::I5 as u8,
    I6 = Reg::I6 as u8,
}

impl TryFrom<Reg> for IndexReg {
    type Error = TryFromRegError;

    fn try_from(value: Reg) -> Result<Self, Self::Error> {
        if value.is_index_reg() {
            Ok(unsafe { mem::transmute(value) })
        } else {
            Err(TryFromRegError(()))
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WordReg {
    A = Reg::A as u8,
    X = Reg::X as u8,
}

impl TryFrom<Reg> for WordReg {
    type Error = TryFromRegError;

    fn try_from(value: Reg) -> Result<Self, Self::Error> {
        if value.is_word_reg() {
            Ok(unsafe { mem::transmute(value) })
        } else {
            Err(TryFromRegError(()))
        }
    }
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Reg {
    A,
    X,
    J,
    I1,
    I2,
    I3,
    I4,
    I5,
    I6,
}

impl Reg {
    pub const fn is_word_reg(self) -> bool {
        use Reg::*;
        matches!(self, A | X)
    }

    pub const fn is_short_reg(self) -> bool {
        use Reg::*;
        matches!(self, J | I1 | I2 | I3 | I4 | I5 | I6)
    }

    pub const fn is_index_reg(self) -> bool {
        use Reg::*;
        matches!(self, I1 | I2 | I3 | I4 | I5 | I6)
    }
}

impl From<WordReg> for Reg {
    fn from(value: WordReg) -> Self {
        unsafe { mem::transmute(value) }
    }
}

impl From<IndexReg> for Reg {
    fn from(value: IndexReg) -> Self {
        unsafe { mem::transmute(value) }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct MachineRegisters {
    reg_a: Word,
    reg_x: Word,
    reg_j: LocationCounter,
    reg_i1: Short,
    reg_i2: Short,
    reg_i3: Short,
    reg_i4: Short,
    reg_i5: Short,
    reg_i6: Short,
}

macro_rules! define_register_access {
    ($($field:ident, $setter:ident, $type:ty, $docname:literal);*;) => {
        $(
            pub const fn $field(&self) -> $type {
                self.$field
            }

            pub const fn $setter(&mut self, new_value: $type) {
                self.$field = new_value;
            }
        )*
    };
}

impl MachineRegisters {
    pub const fn new() -> Self {
        MachineRegisters {
            reg_a: Word::POS_ZERO,
            reg_x: Word::POS_ZERO,
            reg_j: LocationCounter::MIN,
            reg_i1: Short::POS_ZERO,
            reg_i2: Short::POS_ZERO,
            reg_i3: Short::POS_ZERO,
            reg_i4: Short::POS_ZERO,
            reg_i5: Short::POS_ZERO,
            reg_i6: Short::POS_ZERO,
        }
    }

    define_register_access! {
        reg_a, set_reg_a, Word, "rA";
        reg_x, set_reg_x, Word, "rX";
        reg_j, set_reg_j, LocationCounter, "rJ";
        reg_i1, set_reg_i1, Short, "rI1";
        reg_i2, set_reg_i2, Short, "rI2";
        reg_i3, set_reg_i3, Short, "rI3";
        reg_i4, set_reg_i4, Short, "rI4";
        reg_i5, set_reg_i5, Short, "rI5";
        reg_i6, set_reg_i6, Short, "rI6";
    }

    /// Set everything to zero.
    pub const fn reset(&mut self) {
        *self = MachineRegisters::new();
    }

    pub const fn word_reg(&self, reg: WordReg) -> Word {
        match reg {
            WordReg::A => self.reg_a,
            WordReg::X => self.reg_x,
        }
    }

    pub const fn set_word_reg(&mut self, reg: WordReg, value: Word) {
        match reg {
            WordReg::A => self.reg_a = value,
            WordReg::X => self.reg_x = value,
        }
    }

    pub const fn index_reg(&self, reg: IndexReg) -> Short {
        match reg {
            IndexReg::I1 => self.reg_i1,
            IndexReg::I2 => self.reg_i2,
            IndexReg::I3 => self.reg_i3,
            IndexReg::I4 => self.reg_i4,
            IndexReg::I5 => self.reg_i5,
            IndexReg::I6 => self.reg_i6,
        }
    }

    pub const fn set_index_reg(&mut self, reg: IndexReg, value: Short) {
        match reg {
            IndexReg::I1 => self.reg_i1 = value,
            IndexReg::I2 => self.reg_i2 = value,
            IndexReg::I3 => self.reg_i3 = value,
            IndexReg::I4 => self.reg_i4 = value,
            IndexReg::I5 => self.reg_i5 = value,
            IndexReg::I6 => self.reg_i6 = value,
        }
    }
}
