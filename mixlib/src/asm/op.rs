use std::error;
use std::fmt;
use std::str::FromStr;

use crate::asm::OpCode;
use crate::num::Byte;

/// Tag describing the allowed fields of an operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpFieldKind {
    /// The operation can specify any field.
    Any,
    /// The operation must specify a field F &equals; 8L &plus; R such
    /// that 0 &le; L &le; R &le; 5 that denotes the field-specification of
    /// a word.
    Word,
    /// The operation must specify a field 0 &le; F &le; 20 which refers to an
    /// IO device on the machine.
    Device,
    /// The operation's field must be the constant specified to distinguish it
    /// from other operations with the same operation code.
    Const(Byte),
}

/// An error returned while parsing an (invalid) operation mnemonic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseOpError(());

impl fmt::Display for ParseOpError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid operation mnemonic")
    }
}

impl error::Error for ParseOpError {}

macro_rules! define_op_field_kind {
    (Const, $default_field:literal) => {
        OpFieldKind::Const(const { Byte::from_u8($default_field).unwrap() })
    };
    ($kind:ident, $_:literal) => {
        OpFieldKind::$kind
    };
}

macro_rules! define_op_matcher {
    (Const, $opcode:ident, $default_field:literal) => {
        (OpCode::$opcode, $default_field)
    };
    (Any, $opcode:ident, $_:literal) => {
        (OpCode::$opcode, _)
    };
    (Word, $opcode:ident, $_:literal) => {
        (OpCode::$opcode, 0..6)
            | (OpCode::$opcode, 9..14)
            | (OpCode::$opcode, 18..22)
            | (OpCode::$opcode, 27..30)
            | (OpCode::$opcode, 36..38)
            | (OpCode::$opcode, 45)
    };
    (Device, $opcode:ident, $_:literal) => {
        (OpCode::$opcode, 0..=20)
    };
}

macro_rules! define_op {
    ($(
        opcode = $opcode:ident,
        name = $name:ident($default_field:literal),
        field_type = $field_type:tt,
        time = $time:literal
    );*;) => {
        /// All unique MIX machine operations.
        #[repr(u8)]
        #[non_exhaustive]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
        pub enum Op {
            #[default]
            $($name,)+
        }

        impl Op {
            /// Default operation field.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::asm::Op;
            /// use mixlib::num::Byte;
            ///
            /// assert_eq!(Op::LDA.default_field(), Byte::try_from(5).unwrap());
            /// ```
            pub const fn default_field(&self) -> Byte {
                match self {
                    $(Self::$name => const {
                        Byte::from_u8($default_field).unwrap() },)*
                }
            }

            /// Allowed fields for this operation.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::asm::{Op, OpFieldKind};
            ///
            /// assert_eq!(Op::LDA.field_kind(), OpFieldKind::Word);
            /// ```
            pub const fn field_kind(&self) -> OpFieldKind {
                match self {
                    $(Self::$name =>
                        define_op_field_kind!($field_type, $default_field),)*
                }
            }

            /// Normal execution time for operation.
            ///
            /// This does not include time lapses during a halt or IO
            /// operation, nor the extra time needed by a `MOVE` instruction
            /// to manipulate memory.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::asm::Op;
            ///
            /// assert_eq!(Op::NOP.execution_time(), 1);
            /// assert_eq!(Op::LDA.execution_time(), 2);
            /// assert_eq!(Op::MUL.execution_time(), 10);
            /// ```
            pub const fn execution_time(&self) -> u64 {
                match self {
                    $(Self::$name => $time,)*
                }
            }

            /// Get the mnemonic name of `self` as a static string slice.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::asm::Op;
            ///
            /// assert_eq!(Op::LDA.to_str(), "LDA");
            /// ```
            pub const fn to_str(&self) -> &'static str {
                match self {
                    $(Self::$name => stringify!($name),)*
                }
            }

            /// The operation code of this operation.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::asm::{Op, OpCode};
            ///
            /// assert_eq!(Op::LDA.opcode(), OpCode::LoadA);
            /// ```
            pub const fn opcode(&self) -> OpCode {
                match self {
                    $(Self::$name => OpCode::$opcode,)*
                }
            }

            /// Utility for identifiying instruction.
            pub const fn from_opcode_and_field(
                opcode: OpCode,
                field: Byte
            ) -> Option<Op> {
                match (opcode, field.to_u8()) {
                    $(
                        define_op_matcher!(
                            $field_type,
                            $opcode,
                            $default_field
                        ) => Some(Self::$name),
                    )*
                    _ => None,
                }
            }
        }

        impl FromStr for Op {
            type Err = ParseOpError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $(stringify!($name) => Ok(Self::$name),)*
                    _ => Err(ParseOpError(()))
                }
            }
        }

        impl fmt::Display for Op {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str(self.to_str())
            }
        }
    };
}

define_op! {
    opcode = Nop,           name = NOP(0),  field_type = Any,    time = 1;
    opcode = Add,           name = ADD(5),  field_type = Word,   time = 2;
    opcode = Add,           name = FADD(6), field_type = Const,  time = 4;
    opcode = Sub,           name = SUB(5),  field_type = Word,   time = 2;
    opcode = Sub,           name = FSUB(6), field_type = Const,  time = 4;
    opcode = Mul,           name = MUL(5),  field_type = Word,   time = 10;
    opcode = Mul,           name = FMUL(6), field_type = Const,  time = 9;
    opcode = Div,           name = DIV(5),  field_type = Word,   time = 12;
    opcode = Div,           name = FDIV(6), field_type = Const,  time = 11;
    opcode = Special,       name = NUM(0),  field_type = Const,  time = 10;
    opcode = Special,       name = CHAR(1), field_type = Const,  time = 10;
    opcode = Special,       name = HLT(2),  field_type = Const,  time = 1;
    opcode = Special,       name = FLOT(6), field_type = Const,  time = 3;
    opcode = Special,       name = FIX(7),  field_type = Const,  time = 3;
    opcode = Shift,         name = SLA(0),  field_type = Const,  time = 2;
    opcode = Shift,         name = SRA(1),  field_type = Const,  time = 2;
    opcode = Shift,         name = SLAX(2), field_type = Const,  time = 2;
    opcode = Shift,         name = SRAX(3), field_type = Const,  time = 2;
    opcode = Shift,         name = SLC(4),  field_type = Const,  time = 2;
    opcode = Shift,         name = SRC(5),  field_type = Const,  time = 2;
    opcode = Shift,         name = SLB(6),  field_type = Const,  time = 2;
    opcode = Shift,         name = SRB(7),  field_type = Const,  time = 2;
    opcode = Move,          name = MOVE(1), field_type = Any,    time = 1;
    opcode = LoadA,         name = LDA(5),  field_type = Word,   time = 2;
    opcode = Load1,         name = LD1(5),  field_type = Word,   time = 2;
    opcode = Load2,         name = LD2(5),  field_type = Word,   time = 2;
    opcode = Load3,         name = LD3(5),  field_type = Word,   time = 2;
    opcode = Load4,         name = LD4(5),  field_type = Word,   time = 2;
    opcode = Load5,         name = LD5(5),  field_type = Word,   time = 2;
    opcode = Load6,         name = LD6(5),  field_type = Word,   time = 2;
    opcode = LoadX,         name = LDX(5),  field_type = Word,   time = 2;
    opcode = LoadANegative, name = LDAN(5), field_type = Word,   time = 2;
    opcode = Load1Negative, name = LD1N(5), field_type = Word,   time = 2;
    opcode = Load2Negative, name = LD2N(5), field_type = Word,   time = 2;
    opcode = Load3Negative, name = LD3N(5), field_type = Word,   time = 2;
    opcode = Load4Negative, name = LD4N(5), field_type = Word,   time = 2;
    opcode = Load5Negative, name = LD5N(5), field_type = Word,   time = 2;
    opcode = Load6Negative, name = LD6N(5), field_type = Word,   time = 2;
    opcode = LoadXNegative, name = LDXN(5), field_type = Word,   time = 2;
    opcode = StoreA,        name = STA(5),  field_type = Word,   time = 2;
    opcode = Store1,        name = ST1(5),  field_type = Word,   time = 2;
    opcode = Store2,        name = ST2(5),  field_type = Word,   time = 2;
    opcode = Store3,        name = ST3(5),  field_type = Word,   time = 2;
    opcode = Store4,        name = ST4(5),  field_type = Word,   time = 2;
    opcode = Store5,        name = ST5(5),  field_type = Word,   time = 2;
    opcode = Store6,        name = ST6(5),  field_type = Word,   time = 2;
    opcode = StoreX,        name = STX(5),  field_type = Word,   time = 2;
    opcode = StoreJ,        name = STJ(2),  field_type = Word,   time = 2;
    opcode = StoreZ,        name = STZ(5),  field_type = Word,   time = 2;
    opcode = JumpBusy,      name = JBUS(0), field_type = Device, time = 1;
    opcode = IoControl,     name = IOC(0),  field_type = Device, time = 1;
    opcode = In,            name = IN(0),   field_type = Device, time = 1;
    opcode = Out,           name = OUT(0),  field_type = Device, time = 1;
    opcode = JumpReady,     name = JRED(0), field_type = Device, time = 1;
    opcode = Jump,          name = JMP(0),  field_type = Const,  time = 1;
    opcode = Jump,          name = JSJ(1),  field_type = Const,  time = 1;
    opcode = Jump,          name = JOV(2),  field_type = Const,  time = 1;
    opcode = Jump,          name = JNOV(3), field_type = Const,  time = 1;
    opcode = Jump,          name = JL(4),   field_type = Const,  time = 1;
    opcode = Jump,          name = JE(5),   field_type = Const,  time = 1;
    opcode = Jump,          name = JG(6),   field_type = Const,  time = 1;
    opcode = Jump,          name = JGE(7),  field_type = Const,  time = 1;
    opcode = Jump,          name = JNE(8),  field_type = Const,  time = 1;
    opcode = Jump,          name = JLE(9),  field_type = Const,  time = 1;
    opcode = JumpA,         name = JAN(0),  field_type = Const,  time = 1;
    opcode = JumpA,         name = JAZ(1),  field_type = Const,  time = 1;
    opcode = JumpA,         name = JAP(2),  field_type = Const,  time = 1;
    opcode = JumpA,         name = JANN(3), field_type = Const,  time = 1;
    opcode = JumpA,         name = JANZ(4), field_type = Const,  time = 1;
    opcode = JumpA,         name = JANP(5), field_type = Const,  time = 1;
    opcode = JumpA,         name = JAE(6),  field_type = Const,  time = 1;
    opcode = JumpA,         name = JAO(7),  field_type = Const,  time = 1;
    opcode = Jump1,         name = J1N(0),  field_type = Const,  time = 1;
    opcode = Jump1,         name = J1Z(1),  field_type = Const,  time = 1;
    opcode = Jump1,         name = J1P(2),  field_type = Const,  time = 1;
    opcode = Jump1,         name = J1NN(3), field_type = Const,  time = 1;
    opcode = Jump1,         name = J1NZ(4), field_type = Const,  time = 1;
    opcode = Jump1,         name = J1NP(5), field_type = Const,  time = 1;
    opcode = Jump2,         name = J2N(0),  field_type = Const,  time = 1;
    opcode = Jump2,         name = J2Z(1),  field_type = Const,  time = 1;
    opcode = Jump2,         name = J2P(2),  field_type = Const,  time = 1;
    opcode = Jump2,         name = J2NN(3), field_type = Const,  time = 1;
    opcode = Jump2,         name = J2NZ(4), field_type = Const,  time = 1;
    opcode = Jump2,         name = J2NP(5), field_type = Const,  time = 1;
    opcode = Jump3,         name = J3N(0),  field_type = Const,  time = 1;
    opcode = Jump3,         name = J3Z(1),  field_type = Const,  time = 1;
    opcode = Jump3,         name = J3P(2),  field_type = Const,  time = 1;
    opcode = Jump3,         name = J3NN(3), field_type = Const,  time = 1;
    opcode = Jump3,         name = J3NZ(4), field_type = Const,  time = 1;
    opcode = Jump3,         name = J3NP(5), field_type = Const,  time = 1;
    opcode = Jump4,         name = J4N(0),  field_type = Const,  time = 1;
    opcode = Jump4,         name = J4Z(1),  field_type = Const,  time = 1;
    opcode = Jump4,         name = J4P(2),  field_type = Const,  time = 1;
    opcode = Jump4,         name = J4NN(3), field_type = Const,  time = 1;
    opcode = Jump4,         name = J4NZ(4), field_type = Const,  time = 1;
    opcode = Jump4,         name = J4NP(5), field_type = Const,  time = 1;
    opcode = Jump5,         name = J5N(0),  field_type = Const,  time = 1;
    opcode = Jump5,         name = J5Z(1),  field_type = Const,  time = 1;
    opcode = Jump5,         name = J5P(2),  field_type = Const,  time = 1;
    opcode = Jump5,         name = J5NN(3), field_type = Const,  time = 1;
    opcode = Jump5,         name = J5NZ(4), field_type = Const,  time = 1;
    opcode = Jump5,         name = J5NP(5), field_type = Const,  time = 1;
    opcode = Jump6,         name = J6N(0),  field_type = Const,  time = 1;
    opcode = Jump6,         name = J6Z(1),  field_type = Const,  time = 1;
    opcode = Jump6,         name = J6P(2),  field_type = Const,  time = 1;
    opcode = Jump6,         name = J6NN(3), field_type = Const,  time = 1;
    opcode = Jump6,         name = J6NZ(4), field_type = Const,  time = 1;
    opcode = Jump6,         name = J6NP(5), field_type = Const,  time = 1;
    opcode = JumpX,         name = JXN(0),  field_type = Const,  time = 1;
    opcode = JumpX,         name = JXZ(1),  field_type = Const,  time = 1;
    opcode = JumpX,         name = JXP(2),  field_type = Const,  time = 1;
    opcode = JumpX,         name = JXNN(3), field_type = Const,  time = 1;
    opcode = JumpX,         name = JXNZ(4), field_type = Const,  time = 1;
    opcode = JumpX,         name = JXNP(5), field_type = Const,  time = 1;
    opcode = JumpX,         name = JXE(6),  field_type = Const,  time = 1;
    opcode = JumpX,         name = JXO(7),  field_type = Const,  time = 1;
    opcode = ModifyA,       name = INCA(0), field_type = Const,  time = 1;
    opcode = ModifyA,       name = DECA(1), field_type = Const,  time = 1;
    opcode = ModifyA,       name = ENTA(2), field_type = Const,  time = 1;
    opcode = ModifyA,       name = ENNA(3), field_type = Const,  time = 1;
    opcode = Modify1,       name = INC1(0), field_type = Const,  time = 1;
    opcode = Modify1,       name = DEC1(1), field_type = Const,  time = 1;
    opcode = Modify1,       name = ENT1(2), field_type = Const,  time = 1;
    opcode = Modify1,       name = ENN1(3), field_type = Const,  time = 1;
    opcode = Modify2,       name = INC2(0), field_type = Const,  time = 1;
    opcode = Modify2,       name = DEC2(1), field_type = Const,  time = 1;
    opcode = Modify2,       name = ENT2(2), field_type = Const,  time = 1;
    opcode = Modify2,       name = ENN2(3), field_type = Const,  time = 1;
    opcode = Modify3,       name = INC3(0), field_type = Const,  time = 1;
    opcode = Modify3,       name = DEC3(1), field_type = Const,  time = 1;
    opcode = Modify3,       name = ENT3(2), field_type = Const,  time = 1;
    opcode = Modify3,       name = ENN3(3), field_type = Const,  time = 1;
    opcode = Modify4,       name = INC4(0), field_type = Const,  time = 1;
    opcode = Modify4,       name = DEC4(1), field_type = Const,  time = 1;
    opcode = Modify4,       name = ENT4(2), field_type = Const,  time = 1;
    opcode = Modify4,       name = ENN4(3), field_type = Const,  time = 1;
    opcode = Modify5,       name = INC5(0), field_type = Const,  time = 1;
    opcode = Modify5,       name = DEC5(1), field_type = Const,  time = 1;
    opcode = Modify5,       name = ENT5(2), field_type = Const,  time = 1;
    opcode = Modify5,       name = ENN5(3), field_type = Const,  time = 1;
    opcode = Modify6,       name = INC6(0), field_type = Const,  time = 1;
    opcode = Modify6,       name = DEC6(1), field_type = Const,  time = 1;
    opcode = Modify6,       name = ENT6(2), field_type = Const,  time = 1;
    opcode = Modify6,       name = ENN6(3), field_type = Const,  time = 1;
    opcode = ModifyX,       name = INCX(0), field_type = Const,  time = 1;
    opcode = ModifyX,       name = DECX(1), field_type = Const,  time = 1;
    opcode = ModifyX,       name = ENTX(2), field_type = Const,  time = 1;
    opcode = ModifyX,       name = ENNX(3), field_type = Const,  time = 1;
    opcode = CompareA,      name = CMPA(5), field_type = Word,   time = 2;
    opcode = CompareA,      name = FCMP(6), field_type = Const,  time = 4;
    opcode = Compare1,      name = CMP1(5), field_type = Word,   time = 2;
    opcode = Compare2,      name = CMP2(5), field_type = Word,   time = 2;
    opcode = Compare3,      name = CMP3(5), field_type = Word,   time = 2;
    opcode = Compare4,      name = CMP4(5), field_type = Word,   time = 2;
    opcode = Compare5,      name = CMP5(5), field_type = Word,   time = 2;
    opcode = Compare6,      name = CMP6(5), field_type = Word,   time = 2;
    opcode = CompareX,      name = CMPX(5), field_type = Word,   time = 2;
}
