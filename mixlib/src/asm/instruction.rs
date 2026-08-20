use std::hash::{Hash, Hasher};
use std::str::FromStr;
use std::{error, fmt, mem};

use crate::asm::OpCode;
use crate::dev::DeviceUnit;
use crate::num::{Byte, FieldSpec, Short, Sign, Word};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvalidOpError(());

impl fmt::Display for InvalidOpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid operation")
    }
}

impl error::Error for InvalidOpError {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvalidInstructionIndexError(());

impl fmt::Display for InvalidInstructionIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid instruction index")
    }
}

impl error::Error for InvalidInstructionIndexError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvalidInstructionErrorKind {
    InvalidIndex,
    InvalidField,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvalidInstructionError {
    kind: InvalidInstructionErrorKind,
}

impl InvalidInstructionError {
    pub fn kind(&self) -> InvalidInstructionErrorKind {
        self.kind
    }
}

impl fmt::Display for InvalidInstructionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            InvalidInstructionErrorKind::InvalidIndex => {
                f.write_str("invalid instruction: invalid index")
            }
            InvalidInstructionErrorKind::InvalidField => {
                f.write_str("invalid instruction: invalid field")
            }
        }
    }
}

impl error::Error for InvalidInstructionError {}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
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

impl TryFrom<Byte> for InstructionIndex {
    type Error = InvalidInstructionIndexError;

    fn try_from(value: Byte) -> Result<Self, Self::Error> {
        if value.to_u8() <= 6 {
            Ok(unsafe { mem::transmute(value) })
        } else {
            Err(InvalidInstructionIndexError(()))
        }
    }
}

impl From<InstructionIndex> for Byte {
    fn from(value: InstructionIndex) -> Self {
        unsafe { mem::transmute(value) }
    }
}

#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstField(Byte);

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct InstructionData {
    op: Op,
    address: Short,
    index: InstructionIndex,
    field: Byte,
}

impl InstructionData {
    fn to_inst(self) -> Instruction {
        unsafe { mem::transmute(self) }
    }
}

impl Instruction {
    pub fn opcode(&self) -> OpCode {
        self.op().opcode()
    }

    pub fn op(&self) -> Op {
        self.to_data().op
    }

    pub fn address(&self) -> Short {
        self.to_data().address
    }

    pub fn field(&self) -> Byte {
        self.to_data().field
    }

    pub fn index(&self) -> InstructionIndex {
        self.to_data().index
    }

    pub fn sign(&self) -> Sign {
        self.address().sign()
    }

    fn to_data(self) -> InstructionData {
        unsafe { mem::transmute(self) }
    }
}

impl PartialEq for Instruction {
    fn eq(&self, other: &Self) -> bool {
        self.to_data() == other.to_data()
    }
}

impl Eq for Instruction {}

impl Hash for Instruction {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_data().hash(state)
    }
}

impl TryFrom<Word> for Instruction {
    type Error = InvalidInstructionError;

    fn try_from(value: Word) -> Result<Self, Self::Error> {
        let (sign, [a1, a2, i, field, c]) = value.to_sign_bytes();
        let address = Short::from_sign_bytes(sign, [a1, a2]);
        let opcode = OpCode::from(c);
        let index = InstructionIndex::try_from(i).map_err(|_| {
            InvalidInstructionError {
                kind: InvalidInstructionErrorKind::InvalidIndex,
            }
        })?;

        let op = Op::match_opcode_field(opcode, field).ok_or(
            InvalidInstructionError {
                kind: InvalidInstructionErrorKind::InvalidField,
            },
        )?;

        Ok(InstructionData { op, address, index, field }.to_inst())
    }
}

impl From<Instruction> for Word {
    fn from(value: Instruction) -> Self {
        let (sign, [a1, a2]) = value.address().to_sign_bytes();
        let i = Byte::from(value.index());
        let f = value.field();
        let c = Byte::from(value.opcode());
        let bytes = [a1, a2, i, f, c];

        Word::from_sign_bytes(sign, bytes)
    }
}

impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

macro_rules! op_matcher {
    ($opcode:ident, ConstField, $default_field:literal) => {
        (OpCode::$opcode, $default_field)
    };
    ($opcode:ident, Byte, $default_field:literal) => {
        (OpCode::$opcode, _)
    };
    ($opcode:ident, FieldSpec, $default_field:literal) => {
        (OpCode::$opcode, 0..6)
            | (OpCode::$opcode, 9..14)
            | (OpCode::$opcode, 18..22)
            | (OpCode::$opcode, 27..30)
            | (OpCode::$opcode, 36..38)
            | (OpCode::$opcode, 45)
    };
    ($opcode:ident, DeviceUnit, $deafult_field:literal) => {
        (OpCode::$opcode, 0..=20)
    };
}

macro_rules! define_inst {
    ($(
        opcode = $opcode:ident,
        name = $name:ident($default_field:literal),
        field = $field:ident,
        time = $time:literal,
        docs = $docs:expr
    );*;) => {
        #[repr(u8)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
        pub enum Op {
            #[default]
            $(
                #[doc = $docs]
                $name,
            )*
        }

        impl Op {
            pub const fn opcode(self) -> OpCode {
                match self {
                    $(Self::$name => OpCode::$opcode,)*
                }
            }

            pub const fn as_str(self) -> &'static str {
                match self {
                    $(Self::$name => stringify!($name),)*
                }
            }

            pub const fn docs(self) -> &'static str {
                match self {
                    $(Self::$name => $docs,)*
                }
            }

            pub const fn execution_time(self) -> u64 {
                match self {
                    $(Self::$name => $time,)*
                }
            }

            pub fn iter() -> impl Iterator<Item = Self> {
                const LEN: usize = [$(Op::$name,)*].len();
                const ALL: [Op; LEN] = [$(Op::$name,)*];
                ALL.iter().copied()
            }

            fn match_opcode_field(opcode: OpCode, field: Byte) -> Option<Op> {
                match (opcode, field.to_u8()) {
                    $(
                        op_matcher!($opcode, $field, $default_field) =>
                            Some(Self::$name),
                    )*
                    _ => None,
                }
            }
        }

        impl FromStr for Op {
            type Err = InvalidOpError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $(stringify!($name) => Ok(Self::$name),)*
                    _ => Err(InvalidOpError(()))
                }
            }
        }

        #[repr(C, u8)]
        #[derive(Debug, Clone, Copy)]
        pub enum Instruction {
            $(
                #[doc = $docs]
                $name {
                    address: Short,
                    index: InstructionIndex,
                    field: $field
                } = Op::$name as u8,
            )*
        }
    };
}

/// Note closing the description of a floating point operation.
#[rustfmt::skip]
macro_rules! float_note {
    () => {
"
Provided by MIX's optional floating point attachment. A floating point
number occupies one word: byte 1 holds the exponent in excess-`q` form,
where `q` is half the byte size, and bytes 2-5 hold the fraction.
"
    };
}

/// Note closing the description of a binary-only operation.
#[rustfmt::skip]
macro_rules! binary_note {
    () => {
"
Available only on binary versions of MIX.
"
    };
}

/// Description of `LDA` and `LDX`.
#[rustfmt::skip]
macro_rules! load_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Load ", $reg, "

`r", $reg, "` is replaced by the field `F` of `CONTENTS(M)`.

A field read as input is shifted to the right-hand end of the register as it
is loaded, and the remaining bytes are cleared to zero. The sign comes from
the field when byte 0 belongs to it, and is `+` otherwise.
"
    )};
}

/// Description of `LD1` through `LD6`.
#[rustfmt::skip]
macro_rules! load_index_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Load ", $reg, "

`r", $reg, "` is replaced by the field `F` of `CONTENTS(M)`, just as in
`LDA`: the field is shifted to the right-hand end of the register, and the
sign comes from the field when byte 0 belongs to it and is `+` otherwise.

An index register holds only two bytes and a sign, and its bytes 1, 2 and 3
are always assumed to be zero. The instruction is undefined if it would set
any of them to something other than zero.
"
    )};
}

/// Description of `LDAN` and `LDXN`.
#[rustfmt::skip]
macro_rules! load_neg_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Load ", $reg, " Negative

`r", $reg, "` is replaced by the field `F` of `CONTENTS(M)`, with the
opposite sign.

A field read as input is shifted to the right-hand end of the register as it
is loaded, and the remaining bytes are cleared to zero. The sign loaded is
the reverse of the field's own sign when byte 0 belongs to the field, and is
`-` otherwise.
"
    )};
}

/// Description of `LD1N` through `LD6N`.
#[rustfmt::skip]
macro_rules! load_neg_index_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Load ", $reg, " Negative

`r", $reg, "` is replaced by the field `F` of `CONTENTS(M)`, with the
opposite sign: the field is shifted to the right-hand end of the register,
and the sign loaded is the reverse of the field's own sign when byte 0
belongs to the field and is `-` otherwise.

An index register holds only two bytes and a sign, and its bytes 1, 2 and 3
are always assumed to be zero. The instruction is undefined if it would set
any of them to something other than zero.
"
    )};
}

/// Description of `STA` and `STX`.
#[rustfmt::skip]
macro_rules! store_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Store ", $reg, "

The field `F` of `CONTENTS(M)` is replaced by part of `r", $reg, "`. The
rest of `CONTENTS(M)` keeps its old value, and the register itself is left
untouched.

On a store the field has the opposite significance from a load: as many
bytes as the field holds are taken from the right-hand end of the register
and shifted left into place. The sign in memory changes only when byte 0
belongs to the field.
"
    )};
}

/// Description of `ST1` through `ST6`.
#[rustfmt::skip]
macro_rules! store_index_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Store ", $reg, "

The field `F` of `CONTENTS(M)` is replaced by part of `r", $reg, "`, exactly
as in `STA`: as many bytes as the field holds are taken from the right-hand
end of the register and shifted left into place, and the sign in memory
changes only when byte 0 belongs to the field.

Bytes 1, 2 and 3 of an index register are zero, so the register behaves here
as a five-byte register whose three most significant bytes are zero.
"
    )};
}

/// Description of `CMPA` and `CMPX`.
#[rustfmt::skip]
macro_rules! compare_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Compare ", $reg, "

The field `F` of `r", $reg, "` is compared with the same field of
`CONTENTS(M)`, and the comparison indicator is set to `LESS`, `EQUAL` or
`GREATER` according to whether the register value is less than, equal to or
greater than the memory value.

If the field leaves out byte 0, both values are taken as nonnegative;
otherwise the signs take part in the comparison. Minus zero equals plus
zero, so a comparison on the `(0:0)` field always comes out `EQUAL`.
"
    )};
}

/// Description of `CMP1` through `CMP6`.
#[rustfmt::skip]
macro_rules! compare_index_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Compare ", $reg, "

The field `F` of `r", $reg, "` is compared with the same field of
`CONTENTS(M)`, and the comparison indicator is set to `LESS`, `EQUAL` or
`GREATER` according to whether the register value is less than, equal to or
greater than the memory value. If the field leaves out byte 0, both values
are taken as nonnegative.

Bytes 1, 2 and 3 of an index register count as zero in the comparison, so a
comparison on the `(1:2)` field can never come out `GREATER`.
"
    )};
}

/// Description of `ENTA`, `ENTX` and `ENT1` through `ENT6`.
#[rustfmt::skip]
macro_rules! enter_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Enter ", $reg, "

The address `M` is loaded into `r", $reg, "`, with the effect of a load from
a memory word holding the signed value of `M`.

`M` serves here as a signed number rather than as the address of a memory
cell, and when it is zero the sign of the instruction is loaded:
`", $mnemonic, " 0` sets the register to `+0`, and
`", $mnemonic, " -0` sets it to `-0`.
"
    )};
}

/// Description of `ENNA`, `ENNX` and `ENN1` through `ENN6`.
#[rustfmt::skip]
macro_rules! enter_neg_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Enter ", $reg, " Negative

The address `M` is loaded into `r", $reg, "` with the opposite sign, with
the effect of a load from a memory word holding the negated signed value of
`M`.

`M` serves here as a signed number rather than as the address of a memory
cell, and when it is zero the reverse of the instruction's sign is loaded:
`", $mnemonic, " 0` sets the register to `-0`, and
`", $mnemonic, " -0` sets it to `+0`.
"
    )};
}

/// Description of `INC1` through `INC6`.
#[rustfmt::skip]
macro_rules! increase_index_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Increase ", $reg, "

The address `M` is added to `r", $reg, "`. `M` serves here as a signed
number rather than as the address of a memory cell.

Overflow must not occur: if the sum does not fit in the two bytes and sign
of an index register, the result of the instruction is undefined.
"
    )};
}

/// Description of `DEC1` through `DEC6`.
#[rustfmt::skip]
macro_rules! decrease_index_docs {
    ($mnemonic:literal, $reg:literal) => {concat!(
"`", $mnemonic, "` - Decrease ", $reg, "

The address `M` is subtracted from `r", $reg, "`. `M` serves here as a
signed number rather than as the address of a memory cell.

Overflow must not occur: if the difference does not fit in the two bytes and
sign of an index register, the result of the instruction is undefined.
"
    )};
}

/// Long form of a register jump condition, used in prose.
#[rustfmt::skip]
macro_rules! jump_cond {
    (N) => { "negative" };
    (Z) => { "zero" };
    (P) => { "positive, that is, greater than zero" };
    (NN) => { "nonnegative, that is, zero or greater" };
    (NZ) => { "nonzero" };
    (NP) => { "nonpositive, that is, zero or negative" };
}

/// Short form of a register jump condition, used in headings.
#[rustfmt::skip]
macro_rules! jump_cond_name {
    (N) => { "negative" };
    (Z) => { "zero" };
    (P) => { "positive" };
    (NN) => { "nonnegative" };
    (NZ) => { "nonzero" };
    (NP) => { "nonpositive" };
}

/// Description of the register jumps, `JAN` through `JXNP`.
#[rustfmt::skip]
macro_rules! jump_docs {
    ($mnemonic:literal, $reg:literal, $cond:ident) => {concat!(
"`", $mnemonic, "` - Jump ", $reg, " ", jump_cond_name!($cond), "

A jump to location `M` occurs if the contents of `r", $reg, "` are
", jump_cond!($cond), "; otherwise nothing happens.

`rJ` is set as it is by `JMP` whenever the jump is taken.
"
    )};
}

/// Description of `JAE`, `JAO`, `JXE` and `JXO`.
#[rustfmt::skip]
macro_rules! jump_parity_docs {
    ($mnemonic:literal, $reg:literal, $parity:literal) => {concat!(
"`", $mnemonic, "` - Jump ", $reg, " ", $parity, "

A jump to location `M` occurs if the contents of `r", $reg, "` are
", $parity, "; otherwise nothing happens.

`rJ` is set as it is by `JMP` whenever the jump is taken.
", binary_note!()
    )};
}

/// Description of `JL`, `JE`, `JG`, `JGE`, `JNE` and `JLE`.
#[rustfmt::skip]
macro_rules! jump_compare_docs {
    ($mnemonic:literal, $name:literal, $cond:literal) => {concat!(
"`", $mnemonic, "` - jump on ", $name, "

A jump to location `M` occurs if the comparison indicator is
", $cond, "; otherwise nothing happens.

The indicator itself is left as it was, so a run of these jumps may test one
comparison several times over.

`rJ` is set as it is by `JMP` whenever the jump is taken.
"
    )};
}

/// Description of `NOP`.
#[rustfmt::skip]
macro_rules! nop_docs {
    () => {
"`NOP` - No Operation

Nothing happens and the instruction is bypassed. Both the address `M` and
the field `F` are ignored.
"
    };
}

/// Description of `ADD`.
#[rustfmt::skip]
macro_rules! add_docs {
    () => {
"`ADD` - Add

`V` is added to `rA`, where `V` is the field `F` of `CONTENTS(M)` taken just
as `LDA` would take it.

If the magnitude of the result is too large for register A, the overflow
toggle is set on and `rA` holds what is left of the sum, as though a `1` had
been carried into a further register to the left of `rA`; otherwise the
toggle is left as it was. If the result is zero, the sign of `rA` does not
change.

Whether a particular sum overflows depends on the byte size, since overflow
occurs when the magnitude of the result exceeds what five bytes can hold.
"
    };
}

/// Description of `FADD`.
#[rustfmt::skip]
macro_rules! fadd_docs {
    () => {concat!(
"`FADD` - Floating Add

`rA` is replaced by the normalized floating point sum of `rA` and the
floating point number in `CONTENTS(M)`, correctly rounded. Either operand is
normalized first if it is not already in normalized form.

No register other than `rA` is affected. If exponent overflow or underflow
occurs, the overflow toggle is turned on and the exponent of the answer is
given modulo the byte size.
", float_note!()
    )};
}

/// Description of `SUB`.
#[rustfmt::skip]
macro_rules! sub_docs {
    () => {
"`SUB` - Subtract

`V` is subtracted from `rA`, where `V` is the field `F` of `CONTENTS(M)`
taken just as `LDA` would take it. The operation is equivalent to `ADD` with
`-V` in place of `V`, and overflow is treated in the same way.
"
    };
}

/// Description of `FSUB`.
#[rustfmt::skip]
macro_rules! fsub_docs {
    () => {concat!(
"`FSUB` - Floating Subtract

`rA` is replaced by the normalized floating point difference of `rA` and the
floating point number in `CONTENTS(M)`, correctly rounded. Either operand is
normalized first if it is not already in normalized form.

No register other than `rA` is affected. If exponent overflow or underflow
occurs, the overflow toggle is turned on and the exponent of the answer is
given modulo the byte size.
", float_note!()
    )};
}

/// Description of `MUL`.
#[rustfmt::skip]
macro_rules! mul_docs {
    () => {
"`MUL` - Multiply

The ten-byte product of `rA` and `V` replaces registers A and X, the more
significant half going to `rA`. Here `V` is the field `F` of `CONTENTS(M)`
taken just as `LDA` would take it.

The signs of `rA` and `rX` are both set to the algebraic sign of the
product: `+` if `rA` and `V` had like signs, `-` if they differed.
"
    };
}

/// Description of `FMUL`.
#[rustfmt::skip]
macro_rules! fmul_docs {
    () => {concat!(
"`FMUL` - Floating Multiply

`rA` is replaced by the normalized floating point product of `rA` and the
floating point number in `CONTENTS(M)`, correctly rounded. Either operand is
normalized first if it is not already in normalized form.

No register other than `rA` is affected. If exponent overflow or underflow
occurs, the overflow toggle is turned on and the exponent of the answer is
given modulo the byte size.
", float_note!()
    )};
}

/// Description of `DIV`.
#[rustfmt::skip]
macro_rules! div_docs {
    () => {
"`DIV` - Divide

The ten-byte number held in registers A and X - written `rAX`, and taking
the sign of `rA` - is divided by `V`, the field `F` of `CONTENTS(M)` taken
just as `LDA` would take it.

The quotient `±⌊|rAX / V|⌋` goes to `rA` and the remainder
`±(|rAX| mod |V|)` to `rX`. The sign of `rA` afterwards is the algebraic
sign of the quotient; the sign of `rX` afterwards is the sign `rA` carried
before.

If `V` is zero, or if the quotient would need more than five bytes - which
is to say whenever `|rA| ≥ |V|` - registers A and X are filled with
undefined information and the overflow toggle is set on.
"
    };
}

/// Description of `FDIV`
#[rustfmt::skip]
macro_rules! fdiv_docs {
    () => {concat!(
"`FDIV` - Floating Divide

`rA` is replaced by the normalized floating point quotient of `rA` divided
by the floating point number in `CONTENTS(M)`, correctly rounded. Either
operand is normalized first if it is not already in normalized form.

No register other than `rA` is affected. If exponent overflow or underflow
occurs, the overflow toggle is turned on and the exponent of the answer is
given modulo the byte size. Division by zero leaves undefined garbage in
`rA`.
", float_note!()
    )};
}

/// Description of `NUM`.
#[rustfmt::skip]
macro_rules! num_docs {
    () => {
"`NUM` - Convert to Numeric

Registers A and X are assumed to hold a ten-byte number in character code.
The magnitude of `rA` is set to the value of that number read as a decimal
integer. `rX` and the sign of `rA` do not change, and `M` is ignored.

Only the units digit of each byte matters: bytes `00`, `10`, `20`, `30`, …
all convert to the digit `0`, bytes `01`, `11`, `21`, … to the digit `1`,
and so on. Overflow is possible, and the result is then retained modulo
`b^5`, where `b` is the byte size.
"
    };
}

/// Description of `CHAR`.
#[rustfmt::skip]
macro_rules! char_docs {
    () => {
"`CHAR` - convert to characters

The value of `rA` is converted to a ten-byte decimal number in character
code, which is placed in registers A and X. The signs of `rA` and `rX` do
not change, and `M` is ignored.

This is the inverse of `NUM`, and prepares a number for output to punched
cards, tape or the line printer.
"
    };
}

/// Description of `HLT`.
#[rustfmt::skip]
macro_rules! hlt_docs {
    () => {
"`HLT` - Halt

The machine stops. When the computer operator restarts it, the net effect is
that of `NOP`.
"
    };
}

/// Description of `FLOT`.
#[rustfmt::skip]
macro_rules! flot_docs {
    () => {concat!(
"`FLOT` - Convert to Floating Point

`rA` is replaced by the normalized floating point number whose value is the
integer `rA` held before, rounded if it does not fit in the four bytes of a
fraction.

If exponent overflow occurs, the overflow toggle is turned on and the
exponent of the answer is given modulo the byte size.
", float_note!()
    )};
}

/// Description of `FIX`.
#[rustfmt::skip]
macro_rules! fix_docs {
    () => {concat!(
"`FIX` - Convert to Fixed Point

`rA` is replaced by the integer `round(rA)`, the floating point value of
`rA` rounded to the nearest integer. A value lying exactly halfway between
two integers is rounded to whichever of them is odd.

If the answer is too large for the register, the overflow toggle is set on
and the result is undefined.
", float_note!()
    )};
}

/// Description of `SLA`.
#[rustfmt::skip]
macro_rules! sla_docs {
    () => {
"`SLA` - Shift Left A

The bytes of `rA` are shifted `M` places to the left. Zeros come in at the
right, and bytes falling off the left are lost. `rX` is not affected.

`M` counts MIX bytes and must be nonnegative. As with every MIX shift, the
signs of `rA` and `rX` are left alone.
"
    };
}

/// Description of `SRA`.
#[rustfmt::skip]
macro_rules! sra_docs {
    () => {
"`SRA` - Shift Right A

The bytes of `rA` are shifted `M` places to the right. Zeros come in at the
left, and bytes falling off the right are lost. `rX` is not affected.

`M` counts MIX bytes and must be nonnegative. As with every MIX shift, the
signs of `rA` and `rX` are left alone.
"
    };
}

/// Description of `SLAX`.
#[rustfmt::skip]
macro_rules! slax_docs {
    () => {
"`SLAX` - Shift Left AX

Registers A and X are shifted `M` places to the left as though they were a
single ten-byte register. Zeros come in at the right of `rX`, and bytes
falling off the left of `rA` are lost.

`M` counts MIX bytes and must be nonnegative. As with every MIX shift, the
signs of `rA` and `rX` are left alone.
"
    };
}

/// Description of `SRAX`.
#[rustfmt::skip]
macro_rules! srax_docs {
    () => {
"`SRAX` - Shift Right AX

Registers A and X are shifted `M` places to the right as though they were a
single ten-byte register. Zeros come in at the left of `rA`, and bytes
falling off the right of `rX` are lost.

`M` counts MIX bytes and must be nonnegative. As with every MIX shift, the
signs of `rA` and `rX` are left alone.
"
    };
}

/// Description of `SLC`.
#[rustfmt::skip]
macro_rules! slc_docs {
    () => {
"`SLC` - Shift Left AX Circular

Registers A and X are shifted `M` places to the left as though they were a
single ten-byte register with its ends joined: each byte leaving the left of
`rA` comes back in at the right of `rX`, so nothing is lost.

`M` counts MIX bytes and must be nonnegative. As with every MIX shift, the
signs of `rA` and `rX` are left alone.
"
    };
}

/// Description of `SRC`.
#[rustfmt::skip]
macro_rules! src_docs {
    () => {
"`SRC` - Shift Right AX Circular

Registers A and X are shifted `M` places to the right as though they were a
single ten-byte register with its ends joined: each byte leaving the right
of `rX` comes back in at the left of `rA`, so nothing is lost.

`M` counts MIX bytes and must be nonnegative. As with every MIX shift, the
signs of `rA` and `rX` are left alone.
"
    };
}

/// Description of `SLB`.
#[rustfmt::skip]
macro_rules! slb_docs {
    () => {concat!(
"`SLB` - Shift Left AX Binary

Registers A and X are shifted `M` binary places to the left as though they
were a single ten-byte register: `|rAX| ← |2^M · rAX| mod b^10`, where `b`
is the byte size.

`M` must be nonnegative. As with every MIX shift, the signs of `rA` and `rX`
are left alone.
", binary_note!()
    )};
}

/// Description of `SRB`.
#[rustfmt::skip]
macro_rules! srb_docs {
    () => {concat!(
"`SRB` - Shift Right AX Binary

Registers A and X are shifted `M` binary places to the right as though they
were a single ten-byte register: `|rAX| ← ⌊|rAX| / 2^M⌋`.

`M` must be nonnegative. As with every MIX shift, the signs of `rA` and `rX`
are left alone.
", binary_note!()
    )};
}

/// Description of `MOVE`.
#[rustfmt::skip]
macro_rules! move_docs {
    () => {
"`MOVE` - Move

The `F` words starting at location `M` are moved to the locations starting
at the address held in `rI1`, and `rI1` is then increased by `F`. If `F` is
zero, nothing happens.

The words are copied one at a time, so overlapping regions can replicate
data. With `F = 3` and `M = 1000`, an `rI1` of 999 shifts three distinct
words down by one, but an `rI1` of 1001 copies `CONTENTS(1000)` into all
three destinations.

`MOVE` takes `1 + 2F` units of time.
"
    };
}

/// Description of `STJ`.
#[rustfmt::skip]
macro_rules! stj_docs {
    () => {
"`STJ` - Store J

The field `F` of `CONTENTS(M)` is replaced by part of `rJ`, which always
behaves as though its sign were `+`. The rest of `CONTENTS(M)` keeps its old
value, and `rJ` itself is left untouched.

The normal field for `STJ` is `(0:2)` rather than `(0:5)`, since the
instruction is almost always used to plant a return address in the address
part of another instruction.
"
    };
}

/// Description of `STZ`.
#[rustfmt::skip]
macro_rules! stz_docs {
    () => {
"`STZ` - Store Zero

The field `F` of `CONTENTS(M)` is cleared to zero: plus zero is stored in
exactly the way `STA` stores `rA`. The rest of `CONTENTS(M)` keeps its old
value.
"
    };
}

/// Description of `JBUS`.
#[rustfmt::skip]
macro_rules! jbus_docs {
    () => {
"`JBUS` - Jump Busy

A jump to location `M` occurs if the unit named by `F` is busy - that is, if
it has not finished the operation last started on it by `IN`, `OUT` or
`IOC`; otherwise nothing happens.

A program can wait for a unit by jumping to the instruction itself: placed
in location 1000, `JBUS 1000(16)` is executed over and over until unit 16 is
ready.

`rJ` is set as it is by `JMP` whenever the jump is taken.
"
    };
}

/// Description of `IOC`.
#[rustfmt::skip]
macro_rules! ioc_docs {
    () => {
"`IOC` - Input-Output Control

The machine waits, if it must, until the unit named by `F` is no longer
busy, and then performs a control operation that depends on the device:

- **Magnetic tape.** `M = 0` rewinds the tape. `M < 0` skips backward `-M`
  blocks, or to the beginning of the tape, whichever comes first. `M > 0`
  skips forward, which is improper past the block last written.
- **Disk or drum.** `M` should be zero. The unit is positioned according to
  `rX`, so that the next `IN` or `OUT` on it takes less time if it uses the
  same `rX` setting.
- **Line printer.** `M` should be zero; the printer skips to the top of the
  following page.
- **Paper tape.** `M` should be zero; the tape is rewound.
"
    };
}

/// Description of `IN`.
#[rustfmt::skip]
macro_rules! in_docs {
    () => {
"`IN` - Input

Transfer of one block from the unit named by `F` into consecutive locations
starting at `M` is begun. The number of words moved is the fixed block size
of that unit.

The machine waits here if an earlier operation on the same unit is still
running. The transfer itself finishes at an unknown future time, depending
on the speed of the device, so the program must not read the words in memory
until the unit is ready again.

On a disk or drum, the 100-word block read is the one picked out by the
current contents of `rX`. Units 16 through 20 transfer in character code,
five characters to a word, and the sign of every word read is set to `+`.
"
    };
}

/// Description of `OUT`.
#[rustfmt::skip]
macro_rules! out_docs {
    () => {
"`OUT` - Output

Transfer of one block from consecutive locations starting at `M` to the unit
named by `F` is begun. The number of words moved is the fixed block size of
that unit.

The machine waits here until the unit is ready. The transfer itself finishes
at an unknown future time, depending on the speed of the device, so the
program must not alter the words in memory until the unit is ready again.

On a disk or drum, the 100-word block written is the one picked out by the
current contents of `rX`. Units 16 through 20 transfer in character code,
five characters to a word, and word signs are ignored.
"
    };
}

/// Description of `JRED`.
#[rustfmt::skip]
macro_rules! jred_docs {
    () => {
"`JRED` - Jump Ready

A jump to location `M` occurs if the unit named by `F` is ready - that is,
if it has finished the operation last started on it by `IN`, `OUT` or `IOC`;
otherwise nothing happens.

`rJ` is set as it is by `JMP` whenever the jump is taken.
"
    };
}

/// Description of `JMP`.
#[rustfmt::skip]
macro_rules! jmp_docs {
    () => {
"`JMP` - Jump

The next instruction is taken from location `M`.

`rJ` is set to the address of the instruction that would have come next had
the jump not been taken, so that a later `STJ` can plant a return address.
Every jump operator except `JSJ` sets `rJ` this way whenever it jumps, and
no other instruction ever changes `rJ`.
"
    };
}

/// Description of `JSJ`.
#[rustfmt::skip]
macro_rules! jsj_docs {
    () => {
"`JSJ` - Jump, Save J

The next instruction is taken from location `M`, exactly as for `JMP`,
except that `rJ` keeps its old value.
"
    };
}

/// Description of `JOV`.
#[rustfmt::skip]
macro_rules! jov_docs {
    () => {
"`JOV` - Jump on Overflow

If the overflow toggle is on, it is turned off and a jump to location `M`
occurs; otherwise nothing happens. Either way the toggle is left off
afterwards.

`rJ` is set as it is by `JMP` whenever the jump is taken.
"
    };
}

/// Description of `JNOV`.
#[rustfmt::skip]
macro_rules! jnov_docs {
    () => {
"`JNOV` - Jump on No Overflow

If the overflow toggle is off, a jump to location `M` occurs; otherwise the
toggle is turned off and nothing else happens. Either way the toggle is left
off afterwards.

`rJ` is set as it is by `JMP` whenever the jump is taken.
"
    };
}

/// Description of `INCA`.
#[rustfmt::skip]
macro_rules! inca_docs {
    () => {
"`INCA` - Increase A

The address `M` is added to `rA`, with the effect of an `ADD` from a memory
word holding the signed value of `M`. Overflow is possible and is treated
just as in `ADD`. `INCA 1`, for instance, increases `rA` by one.

`M` serves here as a signed number rather than as the address of a memory cell.
"
    };
}

/// Description of `DECA`.
#[rustfmt::skip]
macro_rules! deca_docs {
    () => {
"`DECA` - Decrease A

The address `M` is subtracted from `rA`, with the effect of a `SUB` from a
memory word holding the signed value of `M`. Overflow is possible and is
treated just as in `ADD`.

`M` serves here as a signed number rather than as the address of a memory cell.
"
    };
}

/// Description of `INCX`.
#[rustfmt::skip]
macro_rules! incx_docs {
    () => {
"`INCX` - Increase X

The address `M` is added to `rX`. If overflow occurs the action is that of
`ADD`, except that `rX` takes the place of `rA`; register A is never
affected by this instruction.

`M` serves here as a signed number rather than as the address of a memory cell.
"
    };
}

/// Description of `DECX`.
#[rustfmt::skip]
macro_rules! decx_docs {
    () => {
"`DECX` - Decrease X

The address `M` is subtracted from `rX`. If overflow occurs the action is
that of `ADD`, except that `rX` takes the place of `rA`; register A is never
affected by this instruction.

`M` serves here as a signed number rather than as the address of a memory cell.
"
    };
}

/// Description of `FCMP`.
#[rustfmt::skip]
macro_rules! fcmp_docs {
    () => {concat!(
"`FCMP` - Floating Compare

The comparison indicator is set to `LESS`, `EQUAL` or `GREATER` according to
whether the floating point number in `rA` is definitely less than,
approximately equal to, or definitely greater than the floating point number
in `CONTENTS(M)`. `rA` itself is not changed.

The comparison is made to within a tolerance rather than exactly: two values
count as approximately equal when they differ by no more than
`ε · max(b^(e₁-q), b^(e₂-q))`, where `e₁` and `e₂` are their exponents, `b`
is the byte size and `q` is the excess. The tolerance `ε` is taken from
location 0.
", float_note!()
    )};
}

define_inst! {
    opcode = Nop,           name = NOP(0),  field = Byte,       time = 1,  docs = nop_docs!();
    opcode = Add,           name = ADD(5),  field = FieldSpec,  time = 2,  docs = add_docs!();
    opcode = Add,           name = FADD(6), field = ConstField, time = 4,  docs = fadd_docs!();
    opcode = Sub,           name = SUB(5),  field = FieldSpec,  time = 2,  docs = sub_docs!();
    opcode = Sub,           name = FSUB(6), field = ConstField, time = 4,  docs = fsub_docs!();
    opcode = Mul,           name = MUL(5),  field = FieldSpec,  time = 10, docs = mul_docs!();
    opcode = Mul,           name = FMUL(6), field = ConstField, time = 9,  docs = fmul_docs!();
    opcode = Div,           name = DIV(5),  field = FieldSpec,  time = 12, docs = div_docs!();
    opcode = Div,           name = FDIV(6), field = ConstField, time = 11, docs = fdiv_docs!();
    opcode = Special,       name = NUM(0),  field = ConstField, time = 10, docs = num_docs!();
    opcode = Special,       name = CHAR(1), field = ConstField, time = 10, docs = char_docs!();
    opcode = Special,       name = HLT(2),  field = ConstField, time = 1,  docs = hlt_docs!();
    opcode = Special,       name = FLOT(6), field = ConstField, time = 3,  docs = flot_docs!();
    opcode = Special,       name = FIX(7),  field = ConstField, time = 3,  docs = fix_docs!();
    opcode = Shift,         name = SLA(0),  field = ConstField, time = 2,  docs = sla_docs!();
    opcode = Shift,         name = SRA(1),  field = ConstField, time = 2,  docs = sra_docs!();
    opcode = Shift,         name = SLAX(2), field = ConstField, time = 2,  docs = slax_docs!();
    opcode = Shift,         name = SRAX(3), field = ConstField, time = 2,  docs = srax_docs!();
    opcode = Shift,         name = SLC(4),  field = ConstField, time = 2,  docs = slc_docs!();
    opcode = Shift,         name = SRC(5),  field = ConstField, time = 2,  docs = src_docs!();
    opcode = Shift,         name = SLB(6),  field = ConstField, time = 2,  docs = slb_docs!();
    opcode = Shift,         name = SRB(7),  field = ConstField, time = 2,  docs = srb_docs!();
    opcode = Move,          name = MOVE(1), field = Byte,       time = 1,  docs = move_docs!();
    opcode = LoadA,         name = LDA(5),  field = FieldSpec,  time = 2,  docs = load_docs!("LDA", "A");
    opcode = Load1,         name = LD1(5),  field = FieldSpec,  time = 2,  docs = load_index_docs!("LD1", "I1");
    opcode = Load2,         name = LD2(5),  field = FieldSpec,  time = 2,  docs = load_index_docs!("LD2", "I2");
    opcode = Load3,         name = LD3(5),  field = FieldSpec,  time = 2,  docs = load_index_docs!("LD3", "I3");
    opcode = Load4,         name = LD4(5),  field = FieldSpec,  time = 2,  docs = load_index_docs!("LD4", "I4");
    opcode = Load5,         name = LD5(5),  field = FieldSpec,  time = 2,  docs = load_index_docs!("LD5", "I5");
    opcode = Load6,         name = LD6(5),  field = FieldSpec,  time = 2,  docs = load_index_docs!("LD6", "I6");
    opcode = LoadX,         name = LDX(5),  field = FieldSpec,  time = 2,  docs = load_docs!("LDX", "X");
    opcode = LoadANegative, name = LDAN(5), field = FieldSpec,  time = 2,  docs = load_neg_docs!("LDAN", "A");
    opcode = Load1Negative, name = LD1N(5), field = FieldSpec,  time = 2,  docs = load_neg_index_docs!("LD1N", "I1");
    opcode = Load2Negative, name = LD2N(5), field = FieldSpec,  time = 2,  docs = load_neg_index_docs!("LD2N", "I2");
    opcode = Load3Negative, name = LD3N(5), field = FieldSpec,  time = 2,  docs = load_neg_index_docs!("LD3N", "I3");
    opcode = Load4Negative, name = LD4N(5), field = FieldSpec,  time = 2,  docs = load_neg_index_docs!("LD4N", "I4");
    opcode = Load5Negative, name = LD5N(5), field = FieldSpec,  time = 2,  docs = load_neg_index_docs!("LD5N", "I5");
    opcode = Load6Negative, name = LD6N(5), field = FieldSpec,  time = 2,  docs = load_neg_index_docs!("LD6N", "I6");
    opcode = LoadXNegative, name = LDXN(5), field = FieldSpec,  time = 2,  docs = load_neg_docs!("LDXN", "X");
    opcode = StoreA,        name = STA(5),  field = FieldSpec,  time = 2,  docs = store_docs!("STA", "A");
    opcode = Store1,        name = ST1(5),  field = FieldSpec,  time = 2,  docs = store_index_docs!("ST1", "I1");
    opcode = Store2,        name = ST2(5),  field = FieldSpec,  time = 2,  docs = store_index_docs!("ST2", "I2");
    opcode = Store3,        name = ST3(5),  field = FieldSpec,  time = 2,  docs = store_index_docs!("ST3", "I3");
    opcode = Store4,        name = ST4(5),  field = FieldSpec,  time = 2,  docs = store_index_docs!("ST4", "I4");
    opcode = Store5,        name = ST5(5),  field = FieldSpec,  time = 2,  docs = store_index_docs!("ST5", "I5");
    opcode = Store6,        name = ST6(5),  field = FieldSpec,  time = 2,  docs = store_index_docs!("ST6", "I6");
    opcode = StoreX,        name = STX(5),  field = FieldSpec,  time = 2,  docs = store_docs!("STX", "X");
    opcode = StoreJ,        name = STJ(2),  field = FieldSpec,  time = 2,  docs = stj_docs!();
    opcode = StoreZ,        name = STZ(5),  field = FieldSpec,  time = 2,  docs = stz_docs!();
    opcode = JumpBusy,      name = JBUS(0), field = DeviceUnit, time = 1,  docs = jbus_docs!();
    opcode = IoControl,     name = IOC(0),  field = DeviceUnit, time = 1,  docs = ioc_docs!();
    opcode = In,            name = IN(0),   field = DeviceUnit, time = 1,  docs = in_docs!();
    opcode = Out,           name = OUT(0),  field = DeviceUnit, time = 1,  docs = out_docs!();
    opcode = JumpReady,     name = JRED(0), field = DeviceUnit, time = 1,  docs = jred_docs!();
    opcode = Jump,          name = JMP(0),  field = ConstField, time = 1,  docs = jmp_docs!();
    opcode = Jump,          name = JSJ(1),  field = ConstField, time = 1,  docs = jsj_docs!();
    opcode = Jump,          name = JOV(2),  field = ConstField, time = 1,  docs = jov_docs!();
    opcode = Jump,          name = JNOV(3), field = ConstField, time = 1,  docs = jnov_docs!();
    opcode = Jump,          name = JL(4),   field = ConstField, time = 1,  docs = jump_compare_docs!("JL", "less", "`LESS`");
    opcode = Jump,          name = JE(5),   field = ConstField, time = 1,  docs = jump_compare_docs!("JE", "equal", "`EQUAL`");
    opcode = Jump,          name = JG(6),   field = ConstField, time = 1,  docs = jump_compare_docs!("JG", "greater", "`GREATER`");
    opcode = Jump,          name = JGE(7),  field = ConstField, time = 1,  docs = jump_compare_docs!("JGE", "greater or equal", "`GREATER` or `EQUAL`");
    opcode = Jump,          name = JNE(8),  field = ConstField, time = 1,  docs = jump_compare_docs!("JNE", "unequal", "`LESS` or `GREATER`");
    opcode = Jump,          name = JLE(9),  field = ConstField, time = 1,  docs = jump_compare_docs!("JLE", "less or equal", "`LESS` or `EQUAL`");
    opcode = JumpA,         name = JAN(0),  field = ConstField, time = 1,  docs = jump_docs!("JAN", "A", N);
    opcode = JumpA,         name = JAZ(1),  field = ConstField, time = 1,  docs = jump_docs!("JAZ", "A", Z);
    opcode = JumpA,         name = JAP(2),  field = ConstField, time = 1,  docs = jump_docs!("JAP", "A", P);
    opcode = JumpA,         name = JANN(3), field = ConstField, time = 1,  docs = jump_docs!("JANN", "A", NN);
    opcode = JumpA,         name = JANZ(4), field = ConstField, time = 1,  docs = jump_docs!("JANZ", "A", NZ);
    opcode = JumpA,         name = JANP(5), field = ConstField, time = 1,  docs = jump_docs!("JANP", "A", NP);
    opcode = JumpA,         name = JAE(6),  field = ConstField, time = 1,  docs = jump_parity_docs!("JAE", "A", "even");
    opcode = JumpA,         name = JAO(7),  field = ConstField, time = 1,  docs = jump_parity_docs!("JAO", "A", "odd");
    opcode = Jump1,         name = J1N(0),  field = ConstField, time = 1,  docs = jump_docs!("J1N", "I1", N);
    opcode = Jump1,         name = J1Z(1),  field = ConstField, time = 1,  docs = jump_docs!("J1Z", "I1", Z);
    opcode = Jump1,         name = J1P(2),  field = ConstField, time = 1,  docs = jump_docs!("J1P", "I1", P);
    opcode = Jump1,         name = J1NN(3), field = ConstField, time = 1,  docs = jump_docs!("J1NN", "I1", NN);
    opcode = Jump1,         name = J1NZ(4), field = ConstField, time = 1,  docs = jump_docs!("J1NZ", "I1", NZ);
    opcode = Jump1,         name = J1NP(5), field = ConstField, time = 1,  docs = jump_docs!("J1NP", "I1", NP);
    opcode = Jump2,         name = J2N(0),  field = ConstField, time = 1,  docs = jump_docs!("J2N", "I2", N);
    opcode = Jump2,         name = J2Z(1),  field = ConstField, time = 1,  docs = jump_docs!("J2Z", "I2", Z);
    opcode = Jump2,         name = J2P(2),  field = ConstField, time = 1,  docs = jump_docs!("J2P", "I2", P);
    opcode = Jump2,         name = J2NN(3), field = ConstField, time = 1,  docs = jump_docs!("J2NN", "I2", NN);
    opcode = Jump2,         name = J2NZ(4), field = ConstField, time = 1,  docs = jump_docs!("J2NZ", "I2", NZ);
    opcode = Jump2,         name = J2NP(5), field = ConstField, time = 1,  docs = jump_docs!("J2NP", "I2", NP);
    opcode = Jump3,         name = J3N(0),  field = ConstField, time = 1,  docs = jump_docs!("J3N", "I3", N);
    opcode = Jump3,         name = J3Z(1),  field = ConstField, time = 1,  docs = jump_docs!("J3Z", "I3", Z);
    opcode = Jump3,         name = J3P(2),  field = ConstField, time = 1,  docs = jump_docs!("J3P", "I3", P);
    opcode = Jump3,         name = J3NN(3), field = ConstField, time = 1,  docs = jump_docs!("J3NN", "I3", NN);
    opcode = Jump3,         name = J3NZ(4), field = ConstField, time = 1,  docs = jump_docs!("J3NZ", "I3", NZ);
    opcode = Jump3,         name = J3NP(5), field = ConstField, time = 1,  docs = jump_docs!("J3NP", "I3", NP);
    opcode = Jump4,         name = J4N(0),  field = ConstField, time = 1,  docs = jump_docs!("J4N", "I4", N);
    opcode = Jump4,         name = J4Z(1),  field = ConstField, time = 1,  docs = jump_docs!("J4Z", "I4", Z);
    opcode = Jump4,         name = J4P(2),  field = ConstField, time = 1,  docs = jump_docs!("J4P", "I4", P);
    opcode = Jump4,         name = J4NN(3), field = ConstField, time = 1,  docs = jump_docs!("J4NN", "I4", NN);
    opcode = Jump4,         name = J4NZ(4), field = ConstField, time = 1,  docs = jump_docs!("J4NZ", "I4", NZ);
    opcode = Jump4,         name = J4NP(5), field = ConstField, time = 1,  docs = jump_docs!("J4NP", "I4", NP);
    opcode = Jump5,         name = J5N(0),  field = ConstField, time = 1,  docs = jump_docs!("J5N", "I5", N);
    opcode = Jump5,         name = J5Z(1),  field = ConstField, time = 1,  docs = jump_docs!("J5Z", "I5", Z);
    opcode = Jump5,         name = J5P(2),  field = ConstField, time = 1,  docs = jump_docs!("J5P", "I5", P);
    opcode = Jump5,         name = J5NN(3), field = ConstField, time = 1,  docs = jump_docs!("J5NN", "I5", NN);
    opcode = Jump5,         name = J5NZ(4), field = ConstField, time = 1,  docs = jump_docs!("J5NZ", "I5", NZ);
    opcode = Jump5,         name = J5NP(5), field = ConstField, time = 1,  docs = jump_docs!("J5NP", "I5", NP);
    opcode = Jump6,         name = J6N(0),  field = ConstField, time = 1,  docs = jump_docs!("J6N", "I6", N);
    opcode = Jump6,         name = J6Z(1),  field = ConstField, time = 1,  docs = jump_docs!("J6Z", "I6", Z);
    opcode = Jump6,         name = J6P(2),  field = ConstField, time = 1,  docs = jump_docs!("J6P", "I6", P);
    opcode = Jump6,         name = J6NN(3), field = ConstField, time = 1,  docs = jump_docs!("J6NN", "I6", NN);
    opcode = Jump6,         name = J6NZ(4), field = ConstField, time = 1,  docs = jump_docs!("J6NZ", "I6", NZ);
    opcode = Jump6,         name = J6NP(5), field = ConstField, time = 1,  docs = jump_docs!("J6NP", "I6", NP);
    opcode = JumpX,         name = JXN(0),  field = ConstField, time = 1,  docs = jump_docs!("JXN", "X", N);
    opcode = JumpX,         name = JXZ(1),  field = ConstField, time = 1,  docs = jump_docs!("JXZ", "X", Z);
    opcode = JumpX,         name = JXP(2),  field = ConstField, time = 1,  docs = jump_docs!("JXP", "X", P);
    opcode = JumpX,         name = JXNN(3), field = ConstField, time = 1,  docs = jump_docs!("JXNN", "X", NN);
    opcode = JumpX,         name = JXNZ(4), field = ConstField, time = 1,  docs = jump_docs!("JXNZ", "X", NZ);
    opcode = JumpX,         name = JXNP(5), field = ConstField, time = 1,  docs = jump_docs!("JXNP", "X", NP);
    opcode = JumpX,         name = JXE(6),  field = ConstField, time = 1,  docs = jump_parity_docs!("JXE", "X", "even");
    opcode = JumpX,         name = JXO(7),  field = ConstField, time = 1,  docs = jump_parity_docs!("JXO", "X", "odd");
    opcode = ModifyA,       name = INCA(0), field = ConstField, time = 1,  docs = inca_docs!();
    opcode = ModifyA,       name = DECA(1), field = ConstField, time = 1,  docs = deca_docs!();
    opcode = ModifyA,       name = ENTA(2), field = ConstField, time = 1,  docs = enter_docs!("ENTA", "A");
    opcode = ModifyA,       name = ENNA(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENNA", "A");
    opcode = Modify1,       name = INC1(0), field = ConstField, time = 1,  docs = increase_index_docs!("INC1", "I1");
    opcode = Modify1,       name = DEC1(1), field = ConstField, time = 1,  docs = decrease_index_docs!("DEC1", "I1");
    opcode = Modify1,       name = ENT1(2), field = ConstField, time = 1,  docs = enter_docs!("ENT1", "I1");
    opcode = Modify1,       name = ENN1(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENN1", "I1");
    opcode = Modify2,       name = INC2(0), field = ConstField, time = 1,  docs = increase_index_docs!("INC2", "I2");
    opcode = Modify2,       name = DEC2(1), field = ConstField, time = 1,  docs = decrease_index_docs!("DEC2", "I2");
    opcode = Modify2,       name = ENT2(2), field = ConstField, time = 1,  docs = enter_docs!("ENT2", "I2");
    opcode = Modify2,       name = ENN2(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENN2", "I2");
    opcode = Modify3,       name = INC3(0), field = ConstField, time = 1,  docs = increase_index_docs!("INC3", "I3");
    opcode = Modify3,       name = DEC3(1), field = ConstField, time = 1,  docs = decrease_index_docs!("DEC3", "I3");
    opcode = Modify3,       name = ENT3(2), field = ConstField, time = 1,  docs = enter_docs!("ENT3", "I3");
    opcode = Modify3,       name = ENN3(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENN3", "I3");
    opcode = Modify4,       name = INC4(0), field = ConstField, time = 1,  docs = increase_index_docs!("INC4", "I4");
    opcode = Modify4,       name = DEC4(1), field = ConstField, time = 1,  docs = decrease_index_docs!("DEC4", "I4");
    opcode = Modify4,       name = ENT4(2), field = ConstField, time = 1,  docs = enter_docs!("ENT4", "I4");
    opcode = Modify4,       name = ENN4(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENN4", "I4");
    opcode = Modify5,       name = INC5(0), field = ConstField, time = 1,  docs = increase_index_docs!("INC5", "I5");
    opcode = Modify5,       name = DEC5(1), field = ConstField, time = 1,  docs = decrease_index_docs!("DEC5", "I5");
    opcode = Modify5,       name = ENT5(2), field = ConstField, time = 1,  docs = enter_docs!("ENT5", "I5");
    opcode = Modify5,       name = ENN5(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENN5", "I5");
    opcode = Modify6,       name = INC6(0), field = ConstField, time = 1,  docs = increase_index_docs!("INC6", "I6");
    opcode = Modify6,       name = DEC6(1), field = ConstField, time = 1,  docs = decrease_index_docs!("DEC6", "I6");
    opcode = Modify6,       name = ENT6(2), field = ConstField, time = 1,  docs = enter_docs!("ENT6", "I6");
    opcode = Modify6,       name = ENN6(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENN6", "I6");
    opcode = ModifyX,       name = INCX(0), field = ConstField, time = 1,  docs = incx_docs!();
    opcode = ModifyX,       name = DECX(1), field = ConstField, time = 1,  docs = decx_docs!();
    opcode = ModifyX,       name = ENTX(2), field = ConstField, time = 1,  docs = enter_docs!("ENTX", "X");
    opcode = ModifyX,       name = ENNX(3), field = ConstField, time = 1,  docs = enter_neg_docs!("ENNX", "X");
    opcode = CompareA,      name = CMPA(5), field = FieldSpec,  time = 2,  docs = compare_docs!("CMPA", "A");
    opcode = CompareA,      name = FCMP(6), field = ConstField, time = 4,  docs = fcmp_docs!();
    opcode = Compare1,      name = CMP1(5), field = FieldSpec,  time = 2,  docs = compare_index_docs!("CMP1", "I1");
    opcode = Compare2,      name = CMP2(5), field = FieldSpec,  time = 2,  docs = compare_index_docs!("CMP2", "I2");
    opcode = Compare3,      name = CMP3(5), field = FieldSpec,  time = 2,  docs = compare_index_docs!("CMP3", "I3");
    opcode = Compare4,      name = CMP4(5), field = FieldSpec,  time = 2,  docs = compare_index_docs!("CMP4", "I4");
    opcode = Compare5,      name = CMP5(5), field = FieldSpec,  time = 2,  docs = compare_index_docs!("CMP5", "I5");
    opcode = Compare6,      name = CMP6(5), field = FieldSpec,  time = 2,  docs = compare_index_docs!("CMP6", "I6");
    opcode = CompareX,      name = CMPX(5), field = FieldSpec,  time = 2,  docs = compare_docs!("CMPX", "X");
}
