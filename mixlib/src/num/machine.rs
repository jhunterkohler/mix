//! MIX machine operations on numeric types.

use std::cmp::Ordering;

use crate::char::Char;
use crate::num::{Byte, Word};

/// Pack into unsigned double word. Unsigned double words are represented as
/// the low 60 bits of a `u64`.
fn pack_udword(hi: Word, lo: Word) -> u64 {
    let hi_bits = (hi.mask_value() as u64) << 30;
    let lo_bits = lo.mask_value() as u64;

    hi_bits | lo_bits
}

/// Unpack an unsigned double word. Uses `hi_signbit` and `lo_signbit` as the
/// high and low sign bits, respectively. Masks out extraneous bits in the
/// double word.
fn unpack_udword(
    hi_signbit: u32,
    lo_signbit: u32,
    value: u64,
) -> (Word, Word) {
    debug_assert!(hi_signbit & !Word::SIGN_MASK == 0);
    debug_assert!(lo_signbit & !Word::SIGN_MASK == 0);

    let hi_value = ((value >> 30) as u32) & Word::VALUE_MASK;
    let lo_value = (value as u32) & Word::VALUE_MASK;
    let hi_word = Word(hi_value | hi_signbit);
    let lo_word = Word(lo_value | lo_signbit);

    (hi_word, lo_word)
}

/// MIX addition.
///
/// This behaves in the manner of the MIX `ADD` instruction with `ra` as
/// rA and `v` as loaded from memory. If the result is zero, the sign of
/// `ra` is retained.
///
/// Returns the output and whether an overflow occurred, in order.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::{word, num::machine};
///
/// let ra = word!(100);
/// let v = word!(200);
/// let (new_ra, overflow) = machine::add(ra, v);
///
/// assert_eq!(new_ra, word!(300));
/// assert_eq!(overflow, false);
/// ```
///
/// On zero:
///
/// ```
/// use mixlib::{word, num::{Sign, machine}};
///
/// let ra = word!(-100);
/// let v = -ra;
/// let (new_ra, overflow) = machine::add(ra, v);
///
/// assert_eq!(new_ra.to_sign_u32(), (Sign::Minus, 0));
/// assert_eq!(overflow, false);
/// ```
///
/// On overflow:
///
/// ```
/// use mixlib::{word, num::{Word, machine}};
///
/// let ra = word!(2);
/// let v = Word::MAX;
/// let (new_ra, overflow) = machine::add(ra, v);
///
/// assert_eq!(new_ra, word!(1));
/// assert_eq!(overflow, true);
/// ```
pub fn add(ra: Word, v: Word) -> (Word, bool) {
    ra.overflowing_add(v)
}

/// MIX subtraction.
///
/// This behaves in the manner of the MIX `SUB` instruction with `ra` as
/// rA and `v` as loaded from memory. If the result is zero, the sign of
/// `ra` is retained.
///
/// Returns the output and whether an overflow occurred, in order.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::num::{self, Word};
///
/// let ra = Word::try_from(100).unwrap();
/// let v = Word::try_from(200).unwrap();
/// let (new_ra, overflow) = num::machine::sub(ra, v);
///
/// assert_eq!(new_ra, Word::try_from(-100).unwrap());
/// assert_eq!(overflow, false);
/// ```
///
/// On zero:
///
/// ```
/// use mixlib::num::{self, Word, Sign};
///
/// let ra = Word::try_from(-123).unwrap();
/// let v = ra;
/// let (new_ra, overflow) = num::machine::sub(ra, v);
///
/// assert_eq!(new_ra.to_sign_u32(), (Sign::Minus, 0));
/// assert_eq!(overflow, false);
/// ```
///
/// On overflow:
///
/// ```
/// use mixlib::num::{self, Word};
///
/// let ra = Word::try_from(2).unwrap();
/// let v = Word::MIN;
/// let (new_ra, overflow) = num::machine::sub(ra, v);
///
/// assert_eq!(new_ra, Word::try_from(1).unwrap());
/// assert_eq!(overflow, true);
/// ```
pub fn sub(ra: Word, v: Word) -> (Word, bool) {
    ra.overflowing_sub(v)
}

/// MIX multiplication.
///
/// This behaves in the manner of the MIX `MUL` instruction with `ra` as rA
/// and `v` as loaded from memory. The sign of the output words are both
/// both equal to the algebraic sign of the product.
///
/// Returns the high and low words (rA and rX) of the result in order.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word};
///
/// let ra = Word::try_from(-123456789).unwrap();
/// let v = Word::try_from(-987654321).unwrap();
/// let (new_ra, new_rx) = num::machine::mul(ra, v);
///
/// assert_eq!(new_ra, Word::try_from(113558611).unwrap());
/// assert_eq!(new_rx, Word::try_from(1006588805).unwrap());
/// ```
pub fn mul(ra: Word, v: Word) -> (Word, Word) {
    let signbit = ra.mask_sign() ^ v.mask_sign();
    let res = ra.mask_value() as u64 * v.mask_value() as u64;
    let hi = (res >> 30) as u32 | signbit;
    let lo = (res as u32 & Word::VALUE_MASK) | signbit;

    (Word(hi), Word(lo))
}

/// MIX division.
///
/// This behaves in the manner of the MIX `DIV` instruction with `ra` as
/// rA, `rx` as rX, and `v` as loaded from memory. If an overflow occurs, the
/// quotient and remainder are guarenteed to be `Word::POS_ZERO`, but general
/// MIX machines do not require this.
///
/// Return the quotient (rA), remain (rX), and whether an overflow occurred,
/// in order.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::num::{self, Word};
///
/// let ra = Word::POS_ZERO;
/// let rx = Word::try_from(17).unwrap();
/// let v = Word::try_from(5).unwrap();
/// let (new_ra, new_rx, overflow) = num::machine::div(ra, rx, v);
///
/// // Quotient.
/// assert_eq!(new_ra, Word::try_from(3).unwrap());
/// // Remainder.
/// assert_eq!(new_rx, Word::try_from(2).unwrap());
/// // Overflow.
/// assert_eq!(overflow, false);
/// ```
///
/// Quotient overflow:
///
/// ```
/// use mixlib::num::{self, Word};
///
/// // Overflow since |rA| >= |V|.
/// let ra = Word::try_from(100).unwrap();
/// let rx = Word::POS_ZERO;
/// let v = Word::try_from(10).unwrap();
/// let (new_ra, new_rx, overflow) = num::machine::div(ra, rx, v);
///
/// assert_eq!(new_ra, Word::POS_ZERO);
/// assert_eq!(new_rx, Word::POS_ZERO);
/// assert_eq!(overflow, true);
/// ```
///
/// Divide by zero:
///
/// ```
/// use mixlib::num::{self, Word};
///
/// // Overflow since V = 0.
/// let ra = Word::try_from(100).unwrap();
/// let rx = Word::POS_ZERO;
/// let v = Word::POS_ZERO;
/// let (new_ra, new_rx, overflow) = num::machine::div(ra, rx, v);
///
/// assert_eq!(new_ra, Word::POS_ZERO);
/// assert_eq!(new_rx, Word::POS_ZERO);
/// assert_eq!(overflow, true);
/// ```
pub fn div(ra: Word, rx: Word, v: Word) -> (Word, Word, bool) {
    // All overflow conditions.
    if v.is_zero() || ra.mask_value() >= v.mask_value() {
        return (Word::POS_ZERO, Word::POS_ZERO, true);
    }

    let num_abs = pack_udword(ra, rx);
    let denom_abs = v.mask_value() as u64;

    let quot_abs = (num_abs / denom_abs) as u32;
    let quot_signbit = ra.mask_sign() ^ v.mask_sign();
    let quot = Word(quot_abs | quot_signbit);

    let rem_abs = (num_abs % denom_abs) as u32;
    let rem_signbit = ra.mask_sign();
    let rem = Word(rem_abs | rem_signbit);

    (quot, rem, false)
}

/// MIX shift left.
///
/// This behaves in the manner of MIX `SLA` instruction with `ra` as rA and
/// `bytes` as the unsigned number of bytes to shift.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
/// let new_ra_1 = num::machine::sla(ra, 0);
/// let new_ra_2 = num::machine::sla(ra, 3);
/// let new_ra_3 = num::machine::sla(ra, 6);
///
/// assert_eq!(new_ra_1, ra);
/// assert_eq!(new_ra_2, make_word(Sign::Minus, [4, 5, 0, 0, 0]));
/// assert_eq!(new_ra_3, Word::NEG_ZERO);
/// ```
pub fn sla(ra: Word, bytes: u32) -> Word {
    let shifted = ra.mask_value().unbounded_shl(bytes.saturating_mul(6));
    let res_value = shifted & Word::VALUE_MASK;
    let res_sign = ra.mask_sign();

    Word(res_sign | res_value)
}

/// MIX shift right.
///
/// This behaves in the manner of MIX `SRA` instruction with `ra` as rA and
/// `bytes` as the unsigned number of bytes to shift.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
/// let new_ra_1 = num::machine::sra(ra, 0);
/// let new_ra_2 = num::machine::sra(ra, 3);
/// let new_ra_3 = num::machine::sra(ra, 6);
///
/// assert_eq!(new_ra_1, ra);
/// assert_eq!(new_ra_2, make_word(Sign::Minus, [0, 0, 0, 1, 2]));
/// assert_eq!(new_ra_3, Word::NEG_ZERO);
/// ```
pub fn sra(ra: Word, bytes: u32) -> Word {
    let shifted = ra.mask_value().unbounded_shr(bytes.saturating_mul(6));
    let res_value = shifted & Word::VALUE_MASK;
    let res_sign = ra.mask_sign();

    Word(res_sign | res_value)
}

/// MIX shift left AX.
///
/// This behaves in the manner of MIX `SLAX` instruction with `ra` as rA, `rx`
/// as rX, and `bytes` as the unsigned number of bytes to shift.
///
/// Returns the new rA and rX values, in order.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
/// let rx = make_word(Sign::Plus, [6, 7, 8, 9, 10]);
/// let (new_ra_1, new_rx_1) = num::machine::slax(ra, rx, 0);
/// let (new_ra_2, new_rx_2) = num::machine::slax(ra, rx, 3);
/// let (new_ra_3, new_rx_3) = num::machine::slax(ra, rx, 12);
///
/// assert_eq!(new_ra_1, ra);
/// assert_eq!(new_rx_1, rx);
/// assert_eq!(new_ra_2, make_word(Sign::Minus, [4, 5, 6, 7, 8]));
/// assert_eq!(new_rx_2, make_word(Sign::Plus, [9, 10, 0, 0, 0]));
/// assert_eq!(new_ra_3, Word::NEG_ZERO);
/// assert_eq!(new_rx_3, Word::POS_ZERO);
/// ```
pub fn slax(ra: Word, rx: Word, bytes: u32) -> (Word, Word) {
    unpack_udword(
        ra.mask_sign(),
        rx.mask_sign(),
        pack_udword(ra, rx).unbounded_shl(bytes.saturating_mul(6)),
    )
}

/// MIX shift right AX.
///
/// This behaves in the manner of MIX `SLAX` instruction with `ra` as rA, `rx`
/// as rX, and `bytes` as the unsigned number of bytes to shift.
///
/// Returns the new rA and rX values, in order.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
/// let rx = make_word(Sign::Plus, [6, 7, 8, 9, 10]);
/// let (new_ra_1, new_rx_1) = num::machine::srax(ra, rx, 0);
/// let (new_ra_2, new_rx_2) = num::machine::srax(ra, rx, 3);
/// let (new_ra_3, new_rx_3) = num::machine::srax(ra, rx, 12);
///
/// assert_eq!(new_ra_1, ra);
/// assert_eq!(new_rx_1, rx);
/// assert_eq!(new_ra_2, make_word(Sign::Minus, [0, 0, 0, 1, 2]));
/// assert_eq!(new_rx_2, make_word(Sign::Plus, [3, 4, 5, 6, 7]));
/// assert_eq!(new_ra_3, Word::NEG_ZERO);
/// assert_eq!(new_rx_3, Word::POS_ZERO);
/// ```
pub fn srax(ra: Word, rx: Word, bytes: u32) -> (Word, Word) {
    unpack_udword(
        ra.mask_sign(),
        rx.mask_sign(),
        pack_udword(ra, rx).unbounded_shr(bytes.saturating_mul(6)),
    )
}

/// MIX shift left circular.
///
/// This behaves in the manner of the MIX `SLC` operation with `ra` as rA,
/// `rx` as rX, and `bytes` as the unsigned number of bytes to shift.
///
/// Returns the new rA and rX values, in order.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
/// let rx = make_word(Sign::Plus, [6, 7, 8, 9, 10]);
/// let (new_ra_1, new_rx_1) = num::machine::slc(ra, rx, 0);
/// let (new_ra_2, new_rx_2) = num::machine::slc(ra, rx, 3);
/// let (new_ra_3, new_rx_3) = num::machine::slc(ra, rx, 12);
///
/// assert_eq!(new_ra_1, ra);
/// assert_eq!(new_rx_1, rx);
/// assert_eq!(new_ra_2, make_word(Sign::Minus, [4, 5, 6, 7, 8]));
/// assert_eq!(new_rx_2, make_word(Sign::Plus, [9, 10, 1, 2, 3]));
/// assert_eq!(new_ra_3, make_word(Sign::Minus, [3, 4, 5, 6, 7]));
/// assert_eq!(new_rx_3, make_word(Sign::Plus, [8, 9, 10, 1, 2]));
/// ```
pub fn slc(ra: Word, rx: Word, bytes: u32) -> (Word, Word) {
    let lbits = 6 * (bytes % 5);
    let rbits = 60 - lbits;
    let uval = pack_udword(ra, rx);

    unpack_udword(
        ra.mask_sign(),
        rx.mask_sign(),
        uval << lbits | uval >> rbits,
    )
}

/// MIX shift right circular.
///
/// This behaves in the manner of the MIX `SRC` operation with `ra` as rA,
/// `rx` as rX, and `bytes` as the unsigned number of bytes to shift.
///
/// Returns the new rA and rX values, in order.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
/// let rx = make_word(Sign::Plus, [6, 7, 8, 9, 10]);
/// let (new_ra_1, new_rx_1) = num::machine::src(ra, rx, 0);
/// let (new_ra_2, new_rx_2) = num::machine::src(ra, rx, 3);
/// let (new_ra_3, new_rx_3) = num::machine::src(ra, rx, 12);
///
/// assert_eq!(new_ra_1, ra);
/// assert_eq!(new_rx_1, rx);
/// assert_eq!(new_ra_2, make_word(Sign::Minus, [8, 9, 10, 1, 2]));
/// assert_eq!(new_rx_2, make_word(Sign::Plus, [3, 4, 5, 6, 7]));
/// assert_eq!(new_ra_3, make_word(Sign::Minus, [9, 10, 1, 2, 3]));
/// assert_eq!(new_rx_3, make_word(Sign::Plus, [4, 5, 6, 7, 8]));
/// ```
pub fn src(ra: Word, rx: Word, bytes: u32) -> (Word, Word) {
    let rbits = 6 * (bytes % 5);
    let lbits = 60 - rbits;
    let uval = pack_udword(ra, rx);

    unpack_udword(
        ra.mask_sign(),
        rx.mask_sign(),
        uval << lbits | uval >> rbits,
    )
}

/// MIX convert to numeric.
///
/// This behaves in the manner of the MIX `NUM` operation with `ra` as rA and
/// `rx` as rX.
///
/// Returns the new value of rA with the numeric code.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = make_word(Sign::Minus, [0, 0, 31, 32, 39]);
/// let rx = make_word(Sign::Plus, [37, 57, 47, 30, 30]);
/// let new_ra = num::machine::num(ra, rx);
///
/// assert_eq!(new_ra, Word::try_from(-12977700).unwrap());
/// ```
pub fn num(ra: Word, rx: Word) -> Word {
    const BYTE_MASK: u64 = Byte::VALUE_MASK as u64;

    let hi = ra.0 as u64;
    let lo = rx.0 as u64;

    let value = 1000000000 * (((hi >> 24) & BYTE_MASK) % 10)
        + 100000000 * (((hi >> 18) & BYTE_MASK) % 10)
        + 10000000 * (((hi >> 12) & BYTE_MASK) % 10)
        + 1000000 * (((hi >> 6) & BYTE_MASK) % 10)
        + 100000 * ((hi & BYTE_MASK) % 10)
        + 10000 * (((lo >> 24) & BYTE_MASK) % 10)
        + 1000 * (((lo >> 18) & BYTE_MASK) % 10)
        + 100 * (((lo >> 12) & BYTE_MASK) % 10)
        + 10 * (((lo >> 6) & BYTE_MASK) % 10)
        + ((lo & BYTE_MASK) % 10);

    let repr = (value as u32 & Word::VALUE_MASK) | ra.mask_sign();

    Word(repr)
}

/// MIX convert to characters.
///
/// This behaves in the manner of the MIX `CHAR` operation with `ra` as rA
/// and `rx` as rX. Note that rX is used only to carry its sign to the output.
///
/// Returns the new values of rA and rX, in order.
///
/// # Examples
///
/// ```
/// use mixlib::num::{self, Word, Byte, Sign};
///
/// let make_word = |sign, bytes: [u8; 5]| {
///     Word::from_sign_bytes(sign, bytes.map(|v| Byte::try_from(v).unwrap()))
/// };
///
/// let ra = Word::try_from(-12977699).unwrap();
/// let rx = Word::POS_ZERO;
/// let (new_ra, new_rx) = num::machine::char(ra, rx);
///
/// assert_eq!(new_ra, make_word(Sign::Minus, [30, 30, 31, 32, 39]));
/// assert_eq!(new_rx, make_word(Sign::Plus, [37, 37, 36, 39, 39]));
/// ```
pub fn char(ra: Word, rx: Word) -> (Word, Word) {
    let mut value = ra.mask_value();
    let mut bytes = 0u64;
    let mut offset = 0;

    while offset != 60 {
        let char_code = (Char::Digit0 as u64) + (value % 10) as u64;

        bytes |= char_code << offset;
        value /= 10;
        offset += 6;
    }

    unpack_udword(ra.mask_sign(), rx.mask_sign(), bytes)
}

struct RawFlt {
    signbit: u32,
    frac: u64,
    exp: i32,
}

const FLT_SIGNBIT: u32 = Word::SIGN_MASK;
const FLT_EXP_MAX: i32 = 63;
const FLT_DIGITS: i32 = 4;
const FLT_BIAS: i32 = 32;

fn flt_neg(flt: RawFlt) -> RawFlt {
    RawFlt { signbit: flt.signbit ^ FLT_SIGNBIT, ..flt }
}

fn flt_unpack(word: Word) -> RawFlt {
    let signbit = word.mask_sign();
    let exp = (word.0 >> 24) as i32 & FLT_EXP_MAX;
    let frac = (word.0 as u64) << 40;

    RawFlt { signbit, frac, exp }
}

fn flt_pack(flt: RawFlt) -> (Word, bool) {
    let overflow = !matches!(flt.exp, 0..64);
    let exp_bits = ((flt.exp & 63) as u32) << 24;
    let frac_bits = (flt.frac >> 40) as u32;

    (Word(flt.signbit | exp_bits | frac_bits), overflow)
}

fn flt_frac_overflow(mut flt: RawFlt) -> RawFlt {
    flt.frac = (flt.frac >> 6) | (1 << 58);
    flt.exp += 1;
    flt
}

fn flt_round(mut flt: RawFlt) -> RawFlt {
    /// Byte::MAX/2 into the 5th byte represented by u64.
    const TAIL_HALF: u64 = 32 << 34;
    const TAIL_MASK: u64 = (1 << 40) - 1;
    const HEAD_ONE: u64 = 1 << 40;

    let tail = flt.frac & TAIL_MASK;
    let head = flt.frac & !TAIL_MASK;

    // If tail is less than half, or we are rounding down to even, round
    // down.
    if tail < TAIL_HALF || (tail == TAIL_HALF && (head & HEAD_ONE == 0)) {
        flt.frac = head;
    } else {
        // Here we round up.
        let (new_frac, overflow) = head.overflowing_add(HEAD_ONE);

        flt.frac = new_frac;
        if overflow {
            // Recurses at most twice.
            return flt_round(flt_frac_overflow(flt));
        }
    }

    flt
}

fn flt_prenorm(mut flt: RawFlt) -> RawFlt {
    if flt.frac == 0 {
        flt.exp = 0;
        return flt;
    }

    let shift = match flt.frac.leading_zeros() {
        0..6 => 0,
        6..12 => 1,
        12..18 => 2,
        18..24 => 3,
        24..30 => 4,
        30..36 => 5,
        36..48 => 6,
        _ => unreachable!(),
    };

    flt.exp -= shift;
    flt.frac <<= 6 * shift;
    flt
}

fn flt_norm(flt: RawFlt) -> RawFlt {
    flt_round(flt_prenorm(flt))
}

fn flt_add(u: RawFlt, mut v: RawFlt) -> RawFlt {
    debug_assert!(u.exp >= v.exp);

    let exp_diff = u.exp - v.exp;
    if exp_diff >= FLT_DIGITS + 2 {
        return u;
    }

    v.frac >>= 6 * exp_diff;

    if u.signbit == v.signbit {
        let (frac, overflow) = u.frac.overflowing_add(v.frac);
        let w = RawFlt { frac, ..u };

        if overflow { flt_frac_overflow(w) } else { w }
    } else if u.frac >= v.frac {
        RawFlt { frac: u.frac - v.frac, ..u }
    } else {
        RawFlt { frac: v.frac - u.frac, signbit: v.signbit, ..u }
    }
}

fn flt_cmp(u: RawFlt, v: RawFlt, epsilon: u64) -> Ordering {
    debug_assert!(u.exp >= v.exp);

    // w = v - u
    let w = flt_add(v, flt_neg(u));

    if w.frac <= epsilon {
        Ordering::Equal
    } else if w.signbit == 0 {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

/// MIX floating point addition.
pub fn fadd(ra: Word, v: Word) -> (Word, bool) {
    let u = flt_prenorm(flt_unpack(ra));
    let v = flt_prenorm(flt_unpack(v));
    let w = if u.exp >= v.exp { flt_add(u, v) } else { flt_add(v, u) };

    flt_pack(flt_norm(w))
}

/// MIX floating point subtraction.
pub fn fsub(ra: Word, v: Word) -> (Word, bool) {
    fadd(ra, v.const_neg())
}

/// MIX floating point multiplication.
pub fn fmul(ra: Word, v: Word) -> (Word, bool) {
    let u = flt_prenorm(flt_unpack(ra));
    let v = flt_prenorm(flt_unpack(v));

    let signbit = u.signbit ^ v.signbit;
    let exp = u.exp + v.exp - FLT_BIAS;
    let frac = (u.frac >> 32) * (v.frac >> 32);
    let w = RawFlt { signbit, frac, exp };

    flt_pack(flt_norm(w))
}

/// MIX floating point division.
pub fn fdiv(ra: Word, v: Word) -> (Word, bool) {
    let u = flt_prenorm(flt_unpack(ra));
    let v = flt_prenorm(flt_unpack(v));

    if v.frac == 0 {
        // Return garbage, but do not set overflow.
        return (Word::POS_ZERO, false);
    }

    let signbit = u.signbit ^ v.signbit;
    let exp = u.exp - v.exp + FLT_BIAS + 1;
    let frac = (u.frac >> 6) / v.frac;
    let w = RawFlt { signbit, frac, exp };

    flt_pack(flt_norm(w))
}

/// MIX fixed point to floating point conversion.
pub fn flot(ra: Word) -> (Word, bool) {
    let signbit = ra.mask_sign();
    let frac = (ra.mask_value() as u64) << 34;
    let exp = FLT_BIAS + 5;

    flt_pack(flt_norm(RawFlt { signbit, frac, exp }))
}

/// MIX floating point comparison.
pub fn fcmp(ra: Word, v: Word, epsilon: Word) -> Ordering {
    let u = flt_prenorm(flt_unpack(ra));
    let v = flt_prenorm(flt_unpack(v));
    let e = (epsilon.mask_value() as u64) << 34;

    if u.exp >= v.exp { flt_cmp(u, v, e) } else { flt_cmp(v, u, e).reverse() }
}

/// MIX floating point to fixed point conversion.
pub fn fix(_ra: Word) -> (Word, bool) {
    todo!()
}

/// MIX shift left AX binary.
pub fn slb(ra: Word, rx: Word, bits: u32) -> (Word, Word) {
    unpack_udword(
        ra.mask_sign(),
        rx.mask_sign(),
        pack_udword(ra, rx).unbounded_shl(bits),
    )
}

/// MIX shift right AX binary.
pub fn srb(ra: Word, rx: Word, bits: u32) -> (Word, Word) {
    unpack_udword(
        ra.mask_sign(),
        rx.mask_sign(),
        pack_udword(ra, rx).unbounded_shr(bits),
    )
}
