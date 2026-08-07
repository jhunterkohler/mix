use std::mem::transmute;

use crate::num::Byte;

/// Operation code of a MIX instruction.
///
/// This code is not unique to each machine operation, but a field in the
/// instruction specification. See [`Op`] for a complete list of
/// operations.
///
/// [`Op`]: crate::asm::Op
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OpCode {
    /// NOP(0)
    Nop = 0,
    /// ADD(0:5), FADD(6)
    Add = 1,
    /// SUB(0:5), FSUB(6)
    Sub = 2,
    /// MUL(0:5), FMUL(6)
    Mul = 3,
    /// DIV(0:5), FDIV(6)
    Div = 4,
    /// NUM(0), CHAR(1), HLT(2), FLOT(6), FIX(7)
    Special = 5,
    /// SLA(0), SRA(1), SLAX(2), SRAX(3), SLC(4), SRC(5), SLB(6), SRB(7)
    Shift = 6,
    /// MOVE(1)
    Move = 7,
    /// LDA(0:5)
    LoadA = 8,
    /// LD1(0:5)
    Load1 = 9,
    /// LD2(0:5)
    Load2 = 10,
    /// LD3(0:5)
    Load3 = 11,
    /// LD4(0:5)
    Load4 = 12,
    /// LD5(0:5)
    Load5 = 13,
    /// LD6(0:5)
    Load6 = 14,
    /// LDX(0:5)
    LoadX = 15,
    /// LDAN(0:5)
    LoadANegative = 16,
    /// LD1N(0:5)
    Load1Negative = 17,
    /// LD2N(0:5)
    Load2Negative = 18,
    /// LD3N(0:5)
    Load3Negative = 19,
    /// LD4N(0:5)
    Load4Negative = 20,
    /// LD5N(0:5)
    Load5Negative = 21,
    /// LD6N(0:5)
    Load6Negative = 22,
    /// LDXN(0:5)
    LoadXNegative = 23,
    /// STDA(0:5)
    StoreA = 24,
    /// STD1(0:5)
    Store1 = 25,
    /// STD2(0:5)
    Store2 = 26,
    /// STD3(0:5)
    Store3 = 27,
    /// STD4(0:5)
    Store4 = 28,
    /// STD5(0:5)
    Store5 = 29,
    /// STD6(0:5)
    Store6 = 30,
    /// STDX(0:5)
    StoreX = 31,
    /// STDJ(0:5)
    StoreJ = 32,
    /// STDZ(0:5)
    StoreZ = 33,
    /// JBUS(0)
    JumpBusy = 34,
    /// IOC(0)
    IoControl = 35,
    /// IN(0)
    In = 36,
    /// OUT(0)
    Out = 37,
    /// JRED(0)
    JumpReady = 38,
    /// JMP(0), JSJ(1), JOV(2), JNOV(3), JL(4), JE(5), JG(6), JGE(7), JNE(8),
    /// JLE(8)
    Jump = 39,
    /// JAN(0), JAZ(1), JAP(2), JANN(3), JANZ(4), JANP(5), JAE(6), JAO(7)
    JumpA = 40,
    /// J1N(0), J1Z(1), J1P(2), J1NN(3), J1NZ(4), J1NP(5)
    Jump1 = 41,
    /// J2N(0), J2Z(1), J2P(2), J2NN(3), J2NZ(4), J2NP(5)
    Jump2 = 42,
    /// J3N(0), J3Z(1), J3P(2), J3NN(3), J3NZ(4), J3NP(5)
    Jump3 = 43,
    /// J4N(0), J4Z(1), J4P(2), J4NN(3), J4NZ(4), J4NP(5)
    Jump4 = 44,
    /// J5N(0), J5Z(1), J5P(2), J5NN(3), J5NZ(4), J5NP(5)
    Jump5 = 45,
    /// J6N(0), J6Z(1), J6P(2), J6NN(3), J6NZ(4), J6NP(5)
    Jump6 = 46,
    /// JXN(0), JXZ(1), JXP(2), JXNN(3), JXNZ(4), JXNP(5), JXE(6), JXO(7)
    JumpX = 47,
    /// INCA(0), DECA(1), ENTA(2), ENNA(3)
    ModifyA = 48,
    /// INC1(0), DEC1(1), ENT1(2), ENN1(3)
    Modify1 = 49,
    /// INC2(0), DEC2(1), ENT2(2), ENN2(3)
    Modify2 = 50,
    /// INC3(0), DEC3(1), ENT3(2), ENN3(3)
    Modify3 = 51,
    /// INC4(0), DEC4(1), ENT4(2), ENN4(3)
    Modify4 = 52,
    /// INC5(0), DEC5(1), ENT5(2), ENN5(3)
    Modify5 = 53,
    /// INC6(0), DEC6(1), ENT6(2), ENN6(3)
    Modify6 = 54,
    /// INCX(0), DECX(1), ENTX(2), ENNX(3)
    ModifyX = 55,
    /// CMPA(0:5), FCMP(6)
    CompareA = 56,
    /// CMP1(0:5)
    Compare1 = 57,
    /// CMP2(0:5)
    Compare2 = 58,
    /// CMP3(0:5)
    Compare3 = 59,
    /// CMP4(0:5)
    Compare4 = 60,
    /// CMP5(0:5)
    Compare5 = 61,
    /// CMP6(0:5)
    Compare6 = 62,
    /// CMPX(0:5)
    CompareX = 63,
}

impl OpCode {
    pub const fn to_byte(self) -> Byte {
        unsafe { transmute(self) }
    }

    pub const fn from_byte(value: Byte) -> OpCode {
        unsafe { transmute(value) }
    }
}

impl From<OpCode> for Byte {
    fn from(value: OpCode) -> Self {
        value.to_byte()
    }
}

impl From<Byte> for OpCode {
    fn from(value: Byte) -> OpCode {
        OpCode::from_byte(value)
    }
}
