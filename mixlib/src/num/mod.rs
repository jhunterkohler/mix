//! MIX numerics.
//!
//! Includes fundamental MIX numeric types like [`Word`], and [`Byte`]. All
//! types are implemented with the assumption that bytes are 6 bits, though
//! not all MIX systems have this.

use std::cmp::Ordering;
use std::fmt;
use std::fmt::Write;
use std::hash::Hash;
use std::hash::Hasher;
use std::io;
use std::mem::transmute;
use std::ops::{Mul, Neg};

use crate::bin::{Decode, Encode, EncodingError};

mod convert;
pub use convert::*;

pub mod machine;

/// Enumeration representing numeric signs.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sign {
    /// Plus sign `+`.
    Plus = 0,
    /// Minus sign `-`.
    Minus = 1,
}

impl Mul for Sign {
    type Output = Sign;

    /// Returns the algebraic multiple of the signs.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::num::Sign;
    ///
    /// assert_eq!(Sign::Plus * Sign::Plus, Sign::Plus);
    /// assert_eq!(Sign::Plus * Sign::Minus, Sign::Minus);
    /// assert_eq!(Sign::Minus * Sign::Plus, Sign::Minus);
    /// assert_eq!(Sign::Minus * Sign::Minus, Sign::Plus);
    /// ```
    fn mul(self, rhs: Self) -> Self::Output {
        unsafe { transmute(self as u8 ^ rhs as u8) }
    }
}

impl Neg for Sign {
    type Output = Self;

    /// Returns the algebraic negation of the sign.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::num::Sign;
    ///
    /// assert_eq!(-Sign::Plus, Sign::Minus);
    /// assert_eq!(-Sign::Minus, Sign::Plus);
    /// ```
    fn neg(self) -> Self::Output {
        unsafe { transmute(1 - self as u8) }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_char(if *self == Sign::Plus { '+' } else { '-' })
    }
}

/// A MIX byte.
///
/// Though a MIX byte can vary in size by its formal definition, we fix our
/// implementation to a 6 bit binary byte for simplicity.
#[repr(transparent)]
#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default,
)]
pub struct Byte(u8);

impl Byte {
    /// The largest value that can be represented by [`Byte`]. Equal to `0`.
    pub const MIN: Byte = Byte(0);

    /// The smallest value that can be represented by [`Byte`]. Equal to
    /// (2<sup>6</sup> &minus; 1)
    pub const MAX: Byte = Byte(Byte::VALUE_MASK);

    /// Converts a [`Byte`] to a `u8`.
    pub const fn to_u8(self) -> u8 {
        self.0
    }

    /// Converts a `u8` to a [`Byte`].
    pub const fn from_u8(value: u8) -> Option<Byte> {
        if value <= Byte::VALUE_MASK { Some(Byte(value)) } else { None }
    }

    /// Converts an `u8` to a [`Byte`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value > Byte::MAX.to_u8()`.
    pub const unsafe fn from_u8_unchecked(value: u8) -> Byte {
        debug_assert!(value <= Byte::VALUE_MASK);
        Byte(value)
    }

    /// Checked addition. Computes `self + rhs`, returning `None` if overflow
    /// occurred.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, num::Byte};
    ///
    /// assert_eq!(byte!(1).checked_add(byte!(2)), Some(byte!(3)));
    /// assert_eq!(Byte::MAX.checked_add(byte!(1)), None);
    /// ```
    pub const fn checked_add(self, rhs: Byte) -> Option<Byte> {
        let (res, overflow) = self.overflowing_add(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Checked subtraction. Computes `self - rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// ```
    /// use mixlib::{byte, num::Byte};
    ///
    /// assert_eq!(byte!(3).checked_sub(byte!(2)), Some(byte!(1)));
    /// assert_eq!(Byte::MIN.checked_sub(byte!(1)), None);
    /// ```
    pub const fn checked_sub(self, rhs: Byte) -> Option<Byte> {
        let (res, overflow) = self.overflowing_sub(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Checked multiplication. Computes `self * rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// ```
    /// use mixlib::{byte, num::Byte};
    ///
    /// assert_eq!(byte!(2).checked_mul(byte!(3)), Some(byte!(6)));
    /// assert_eq!(Byte::MAX.checked_mul(byte!(2)), None);
    /// ```
    pub const fn checked_mul(self, rhs: Byte) -> Option<Byte> {
        let (res, overflow) = self.overflowing_mul(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Overflowing addition. Computes `self + rhs`, returning the value and
    /// carry.
    ///
    /// ```
    /// use mixlib::{byte, num::Byte};
    ///
    /// assert_eq!(byte!(1).overflowing_add(byte!(2)), (byte!(3), false));
    /// assert_eq!(Byte::MAX.overflowing_add(byte!(2)), (byte!(1), true));
    /// ```
    pub const fn overflowing_add(self, rhs: Byte) -> (Byte, bool) {
        let value = self.0 + rhs.0;
        (Byte(value & Byte::VALUE_MASK), value > Byte::VALUE_MASK)
    }

    /// Overflowing subtraction. Computes `self + rhs`, returning the value
    /// and carry.
    ///
    /// ```
    /// use mixlib::{byte, num::Byte};
    ///
    /// assert_eq!(byte!(3).overflowing_sub(byte!(2)), (byte!(1), false));
    /// assert_eq!(Byte::MIN.overflowing_sub(byte!(1)), (Byte::MAX, true));
    /// ```
    pub const fn overflowing_sub(self, rhs: Byte) -> (Byte, bool) {
        (Byte(Byte::VALUE_MASK & (self.0.wrapping_sub(rhs.0))), self.0 < rhs.0)
    }

    /// Overflowing multiplication. Computes `self * rhs`, returning the value
    /// and wether an overflow occurred.
    ///
    /// ```
    /// use mixlib::byte;
    ///
    /// assert_eq!(byte!(2).overflowing_mul(byte!(3)), (byte!(6), false));
    /// assert_eq!(byte!(10).overflowing_mul(byte!(10)), (byte!(36), true));
    /// ```
    pub const fn overflowing_mul(self, rhs: Byte) -> (Byte, bool) {
        let value = self.0 as u16 * rhs.0 as u16;
        let masked = (value & Byte::VALUE_MASK as u16) as u8;

        (Byte(masked), value > Byte::VALUE_MASK as u16)
    }

    const VALUE_MASK: u8 = (1 << 6) - 1;
}

impl fmt::Display for Byte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Encode for Byte {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.0.encode(w)
    }
}

impl Decode for Byte {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        Byte::from_u8(u8::decode(r)?)
            .ok_or_else(|| io::Error::other(EncodingError))
    }
}

/// A MIX short integer.
///
/// We say a `short` is the two byte signed integers used in MIX index
/// registers and the instruction address parameter.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Short(u16);

impl Short {
    /// The smallest value that can be represented by [`Short`]. Equal to
    /// &minus;(2<sup>12</sup> &minus; 1).
    pub const MIN: Short = Short(Short::SIGN_MASK | Short::VALUE_MASK);

    /// The largest value that can be represented by [`Short`]. Equal to
    /// (2<sup>12</sup> &minus; 1).
    pub const MAX: Short = Short(Short::VALUE_MASK);

    /// The positive zero value &plus;0.
    pub const POS_ZERO: Short = Short(0);

    /// The negative zero value &minus;0.
    pub const NEG_ZERO: Short = Short(Short::SIGN_MASK);

    /// Converts a [`Short`] to `i16`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// assert_eq!(short!(-12).to_i16(), -12);
    /// assert_eq!(Short::POS_ZERO.to_i16(), 0);
    /// assert_eq!(Short::NEG_ZERO.to_i16(), 0);
    /// ```
    pub const fn to_i16(self) -> i16 {
        if self.mask_sign() == 0 {
            self.0 as i16
        } else {
            -(self.mask_value() as i16)
        }
    }

    /// Converts a `i16` to a [`Short`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::{Short, Sign}};
    ///
    /// assert_eq!(Short::from_i16(-10), Some(short!(-10)));
    /// assert_eq!(Short::from_i16(Short::MAX.to_i16() + 1), None);
    /// assert_eq!(Short::from_i16(0), Some(Short::POS_ZERO));
    /// assert_eq!(Short::from_i16(0).unwrap().sign(), Sign::Plus);
    /// ```
    pub const fn from_i16(value: i16) -> Option<Short> {
        if value >= 0 {
            Self::from_sign_u16(Sign::Plus, value as u16)
        } else {
            Self::from_sign_u16(Sign::Minus, -value as u16)
        }
    }

    /// Converts a `i16` to a [`Short`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This causes undefined behavior if `value < Short::MIN.to_i16()` or
    /// `value > Short::MAX.to_i16()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::{Short, Sign}};
    ///
    /// assert_eq!(unsafe { Short::from_i16_unchecked(-12) }, short!(-12));
    /// assert_eq!(unsafe { Short::from_i16_unchecked(0) }, Short::POS_ZERO);
    /// assert_eq!(unsafe { Short::from_i16_unchecked(0) }.sign(), Sign::Plus);
    /// ```
    pub const unsafe fn from_i16_unchecked(value: i16) -> Short {
        debug_assert!(value.unsigned_abs() <= Short::VALUE_MASK);
        unsafe {
            if value >= 0 {
                Self::from_sign_u16_unchecked(Sign::Plus, value as u16)
            } else {
                Self::from_sign_u16_unchecked(Sign::Minus, -value as u16)
            }
        }
    }

    /// Converts a [`Short`] to [`Sign`] and `u16`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Sign};
    ///
    /// assert_eq!(short!(-123).to_sign_u16(), (Sign::Minus, 123));
    /// ```
    pub const fn to_sign_u16(self) -> (Sign, u16) {
        (self.sign(), self.magnitude())
    }

    /// Converts a [`Sign`] and `u16` to a [`Short`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::{Short, Sign}};
    ///
    /// assert_eq!(Short::from_sign_u16(Sign::Minus, 12), Some(short!(-12)));
    /// assert_eq!(Short::from_sign_u16(Sign::Plus, 5000), None);
    /// ```
    pub const fn from_sign_u16(sign: Sign, magnitude: u16) -> Option<Short> {
        if magnitude <= Short::VALUE_MASK {
            // SAFETY: Ensured that magnitude is valid.
            Some(unsafe { Short::from_sign_u16_unchecked(sign, magnitude) })
        } else {
            None
        }
    }

    /// Converts a [`Sign`] and `u16` to a [`Short`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This causes undefined behavior if `magnitude >
    /// Short::MAX.to_i16().unsigned_abs()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::{Short, Sign}};
    ///
    /// assert_eq!(
    ///     unsafe { Short::from_sign_u16_unchecked(Sign::Minus, 10) },
    ///     short!(-10)
    /// );
    /// ```
    pub const unsafe fn from_sign_u16_unchecked(
        sign: Sign,
        magnitude: u16,
    ) -> Short {
        debug_assert!(magnitude <= Short::VALUE_MASK);
        Short(((sign as u16) << 12) | magnitude)
    }

    /// Converts a sign/bytes representation to a [`Short`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, short, num::{Sign, Short}};
    ///
    /// assert_eq!(
    ///     Short::from_sign_bytes(Sign::Minus, [byte!(1), byte!(2)]),
    ///     short![-, 1, 2]
    /// );
    /// ```
    pub const fn from_sign_bytes(sign: Sign, bytes: [Byte; 2]) -> Short {
        let sign_bit = (sign as u16) << 12;
        let value_bits = (bytes[0].0 as u16) << 6 | bytes[1].0 as u16;

        Short(sign_bit | value_bits)
    }

    /// Converts a [`Short`] to its sign/bytes representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, short, num::Sign};
    ///
    /// assert_eq!(
    ///     short![-, 1, 2].to_sign_bytes(),
    ///     (Sign::Minus, [byte!(1), byte!(2)])
    /// );
    /// ```
    pub const fn to_sign_bytes(self) -> (Sign, [Byte; 2]) {
        (self.sign(), self.bytes())
    }

    /// Returns the sign of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::{Sign, Short}};
    ///
    /// assert_eq!(short!(1).sign(), Sign::Plus);
    /// assert_eq!(short!(-1).sign(), Sign::Minus);
    /// assert_eq!(Short::MAX.sign(), Sign::Plus);
    /// assert_eq!(Short::MIN.sign(), Sign::Minus);
    /// assert_eq!(Short::POS_ZERO.sign(), Sign::Plus);
    /// assert_eq!(Short::NEG_ZERO.sign(), Sign::Minus);
    /// ```
    pub const fn sign(self) -> Sign {
        unsafe { transmute(((self.mask_sign()) >> 12) as u8) }
    }

    /// Returns the magnitude of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// assert_eq!(short!(1).magnitude(), 1);
    /// assert_eq!(short!(-1).magnitude(), 1);
    /// assert_eq!(Short::MAX.magnitude(), 4095);
    /// assert_eq!(Short::MIN.magnitude(), 4095);
    /// assert_eq!(Short::POS_ZERO.magnitude(), 0);
    /// assert_eq!(Short::NEG_ZERO.magnitude(), 0);
    /// ```
    pub const fn magnitude(self) -> u16 {
        self.mask_value()
    }

    /// Return the bytes of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, short};
    ///
    /// assert_eq!(short![-, 1, 2].bytes(), [byte!(1), byte!(2)]);
    /// ```
    pub const fn bytes(self) -> [Byte; 2] {
        [
            Byte((self.0 >> 6) as u8 & Byte::VALUE_MASK),
            Byte(self.0 as u8 & Byte::VALUE_MASK),
        ]
    }

    /// Returns `true` if `self` is positive or negative zero and `false`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// // Positive
    /// assert!(!short!(1).is_zero());
    /// assert!(!Short::MAX.is_zero());
    ///
    /// // Negative
    /// assert!(!short!(-1).is_zero());
    /// assert!(!Short::MIN.is_zero());
    ///
    /// // Zero
    /// assert!(Short::POS_ZERO.is_zero());
    /// assert!(Short::NEG_ZERO.is_zero());
    /// ```
    pub const fn is_zero(self) -> bool {
        self.mask_value() == 0
    }

    /// Returns `true` if `self` is positive and false if `self` is zero or
    /// negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// // Positive
    /// assert!(short!(1).is_positive());
    /// assert!(Short::MAX.is_positive());
    ///
    /// // Negative
    /// assert!(!short!(-1).is_positive());
    /// assert!(!Short::MIN.is_positive());
    ///
    /// // Zero
    /// assert!(!Short::POS_ZERO.is_positive());
    /// assert!(!Short::NEG_ZERO.is_positive());
    /// ```
    pub const fn is_positive(self) -> bool {
        self.mask_sign() == 0 && self.mask_value() != 0
    }

    /// Returns `true` if `self` is negative and false if `self` is zero or
    /// positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// // Positive
    /// assert!(!short!(1).is_negative());
    /// assert!(!Short::MAX.is_negative());
    ///
    /// // Negative
    /// assert!(short!(-1).is_negative());
    /// assert!(Short::MIN.is_negative());
    ///
    /// // Zero
    /// assert!(!Short::POS_ZERO.is_negative());
    /// assert!(!Short::NEG_ZERO.is_negative());
    /// ```
    pub const fn is_negative(self) -> bool {
        self.mask_sign() != 0 && self.mask_value() != 0
    }

    pub const fn is_even(self) -> bool {
        self.0 & 1 == 0
    }

    /// Compute the absolute value of `self`.
    ///
    /// Effectively sets the sign of `self` to [`Sign::Plus`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::short;
    ///
    /// assert_eq!(short!(1).abs(), short!(1));
    /// assert_eq!(short!(-1).abs(), short!(1));
    /// ```
    pub const fn abs(self) -> Short {
        Short(self.mask_value())
    }

    /// Checked addition. Computes `self + rhs`, returning `None` if overflow
    /// occurred.
    ///
    /// The sign of `self` is retained if the result is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// assert_eq!(short!(1).checked_add(short!(2)), Some(short!(3)));
    /// assert_eq!(Short::MAX.checked_add(short!(1)), None);
    /// ```
    pub const fn checked_add(self, rhs: Short) -> Option<Short> {
        let (res, overflow) = self.overflowing_add(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Checked subtraction. Computes `self - rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// The sign of `self` is retained if the result is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// assert_eq!(short!(3).checked_sub(short!(2)), Some(short!(1)));
    /// assert_eq!(Short::MIN.checked_sub(short!(1)), None);
    /// ```
    pub const fn checked_sub(self, rhs: Short) -> Option<Short> {
        let (res, overflow) = self.overflowing_sub(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Checked multiplication. Computes `self * rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// The sign of the result is `self.sign() * rhs.sign()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{short, num::Short};
    ///
    /// assert_eq!(short!(10).checked_mul(short!(100)), Some(short!(1000)));
    /// assert_eq!(Short::MAX.checked_mul(short!(2)), None);
    /// ```
    pub const fn checked_mul(self, rhs: Short) -> Option<Short> {
        let (res, overflow) = self.overflowing_mul(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Overflowing addition. Computes `self + rhs`, returning the value and
    /// carry.
    ///
    /// If the result is zero, the sign of `self` is retained.
    pub const fn overflowing_add(self, rhs: Short) -> (Short, bool) {
        let lhs_value = self.mask_value();
        let lhs_sign = self.mask_sign();
        let rhs_value = rhs.mask_value();
        let rhs_sign = rhs.mask_sign();

        if lhs_sign == rhs_sign {
            let added = lhs_value + rhs_value;
            let res_value = added & Short::VALUE_MASK;
            let overflow = added > Short::VALUE_MASK;

            (Short(lhs_sign | res_value), overflow)
        } else if lhs_value >= rhs_value {
            // Propogates sign of `self` on zero.
            (Short(lhs_sign | (lhs_value - rhs_value)), false)
        } else {
            (Short(rhs_sign | (rhs_value - lhs_value)), false)
        }
    }

    /// Overflowing subtraction. Computes `self + rhs`, returning the value
    /// and carry.
    ///
    /// If the result is zero, the sign of `self` is retained.
    pub const fn overflowing_sub(self, rhs: Short) -> (Short, bool) {
        self.overflowing_add(rhs.const_neg())
    }

    /// Overflowing multiplication. Computes `self * rhs`, returning the value
    /// and wether an overflow occurred.
    ///
    /// The sign of the result is `self.sign() * rhs.sign()`.
    pub const fn overflowing_mul(self, rhs: Short) -> (Short, bool) {
        let res_sign = self.mask_sign() ^ rhs.mask_sign();

        // Must promote to u32 to fit 24 bits.
        let mulled = self.mask_value() as u32 * rhs.mask_value() as u32;
        let res_value = mulled as u16 & Self::VALUE_MASK;
        let overflow = mulled > Self::VALUE_MASK as u32;

        (Short(res_sign | res_value), overflow)
    }

    pub const fn with_sign(self, sign: Sign) -> Short {
        let sign_bit = (sign as u16) << 12;
        let value_bits = self.mask_value();

        Short(sign_bit | value_bits)
    }

    const SIGN_MASK: u16 = 1 << 12;
    const VALUE_MASK: u16 = (1 << 12) - 1;
    const MASK: u16 = Self::SIGN_MASK | Self::VALUE_MASK;

    const fn mask_sign(self) -> u16 {
        self.0 & Short::SIGN_MASK
    }

    const fn mask_value(self) -> u16 {
        self.0 & Short::VALUE_MASK
    }

    const fn const_neg(self) -> Short {
        Short(self.0 ^ Short::SIGN_MASK)
    }

    pub(crate) const fn zero_extend_to_word(self) -> Word {
        let sign_bit = (self.mask_sign() as u32) << 18;
        let value_bits = self.mask_value() as u32;

        Word(sign_bit | value_bits)
    }
}

impl Neg for Short {
    type Output = Short;

    fn neg(self) -> Self::Output {
        self.const_neg()
    }
}

impl PartialEq for Short {
    fn eq(&self, other: &Self) -> bool {
        self.to_i16() == other.to_i16()
    }
}

impl Eq for Short {}

impl PartialOrd for Short {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Short {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_i16().cmp(&other.to_i16())
    }
}

impl Hash for Short {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_i16().hash(state);
    }
}

impl fmt::Display for Short {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad_integral(
            self.mask_sign() == 0,
            "",
            &self.mask_value().to_string(),
        )
    }
}

impl Encode for Short {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.0.encode(w)
    }
}

impl Decode for Short {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        let repr = u16::decode(r)?;
        if repr & !Short::MASK == 0 {
            Ok(Short(repr))
        } else {
            Err(io::Error::other(EncodingError))
        }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default)]
pub struct Word(u32);

impl Word {
    /// The largest value that can be represented by [`Word`]. Equal to
    /// (2<sup>30</sup> &minus; 1).
    pub const MAX: Word = Word(Word::VALUE_MASK);

    /// The smallest value that can be represented by [`Word`]. Equal to
    /// &minus;(2<sup>30</sup> &minus; 1).
    pub const MIN: Word = Word(Word::VALUE_MASK | Word::SIGN_MASK);

    /// The positive zero value &plus;0.
    pub const POS_ZERO: Word = Word(0);

    /// The negative zero value &minus;0.
    pub const NEG_ZERO: Word = Word(Word::SIGN_MASK);

    /// Converts a [`Word`] to `i32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Word};
    ///
    /// assert_eq!(word!(-12).to_i32(), -12);
    /// assert_eq!(Word::POS_ZERO.to_i32(), 0);
    /// assert_eq!(Word::NEG_ZERO.to_i32(), 0);
    /// ```
    pub const fn to_i32(self) -> i32 {
        if self.mask_sign() == 0 {
            self.0 as i32
        } else {
            -(self.mask_value() as i32)
        }
    }

    /// Converts a `i32` to a [`Word`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Word, Sign}};
    ///
    /// assert_eq!(Word::from_i32(-1), Some(word!(-1)));
    /// assert_eq!(Word::from_i32(0), Some(Word::POS_ZERO));
    /// assert_eq!(Word::from_i32(0).unwrap().sign(), Sign::Plus);
    /// assert_eq!(Word::from_i32(Word::MAX.to_i32() + 1), None);
    /// ```
    pub const fn from_i32(value: i32) -> Option<Word> {
        if value >= 0 {
            Word::from_sign_u32(Sign::Plus, value as u32)
        } else {
            Word::from_sign_u32(Sign::Minus, -value as u32)
        }
    }

    /// Converts a `i32` to a [`Word`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This causes undefined behavior if `value < Word::MIN.to_i32()` or
    /// `value > Word::MAX.to_i32()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Word, Sign}};
    ///
    /// assert_eq!(unsafe { Word::from_i32_unchecked(-1) }, word!(-1));
    /// assert_eq!(unsafe { Word::from_i32_unchecked(0) }, Word::POS_ZERO);
    /// assert_eq!(unsafe { Word::from_i32_unchecked(0) }.sign(), Sign::Plus);
    /// ```
    pub const unsafe fn from_i32_unchecked(value: i32) -> Word {
        debug_assert!(value.unsigned_abs() <= Word::VALUE_MASK);
        unsafe {
            if value >= 0 {
                Word::from_sign_u32_unchecked(Sign::Plus, value as u32)
            } else {
                Word::from_sign_u32_unchecked(Sign::Minus, -value as u32)
            }
        }
    }

    /// Converts a [`Word`] to [`Sign`] and `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Sign};
    ///
    /// assert_eq!(word!(-123).to_sign_u32(), (Sign::Minus, 123));
    /// ```
    pub const fn to_sign_u32(self) -> (Sign, u32) {
        (self.sign(), self.magnitude())
    }

    /// Converts a [`Sign`] and `u32` to a [`Word`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Word, Sign}};
    ///
    /// assert_eq!(Word::from_sign_u32(Sign::Minus, 12), Some(word!(-12)));
    /// assert_eq!(
    ///     Word::from_sign_u32(Sign::Plus, Word::MAX.magnitude() + 1),
    ///     None
    /// );
    /// ```
    pub const fn from_sign_u32(sign: Sign, magnitude: u32) -> Option<Word> {
        if magnitude <= Word::VALUE_MASK {
            // SAFETY: Ensured that magnitude is valid.
            Some(unsafe { Word::from_sign_u32_unchecked(sign, magnitude) })
        } else {
            None
        }
    }

    /// Converts a [`Sign`] and `u32` to a [`Word`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This causes undefined behavior if `magnitude >
    /// Word::MAX.to_i32().unsigned_abs()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Word, Sign}};
    ///
    /// assert_eq!(
    ///     unsafe { Word::from_sign_u32_unchecked(Sign::Minus, 12) },
    ///     word!(-12)
    /// );
    /// ```
    pub const unsafe fn from_sign_u32_unchecked(
        sign: Sign,
        magnitude: u32,
    ) -> Word {
        debug_assert!(magnitude <= Word::VALUE_MASK);
        Word(((sign as u32) << 30) | magnitude)
    }

    /// Converts a sign/bytes representation to a [`Word`].
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, word, num::{Sign, Word}};
    ///
    /// let sign = Sign::Minus;
    /// let bytes = [byte!(1), byte!(2), byte!(3), byte!(4), byte!(5)];
    ///
    /// assert_eq!(
    ///     Word::from_sign_bytes(sign, bytes),
    ///     word![-, 1, 2, 3, 4, 5]
    /// );
    /// ```
    pub const fn from_sign_bytes(sign: Sign, bytes: [Byte; 5]) -> Word {
        let signbit = (sign as u32) << 30;
        let value = (bytes[0].0 as u32) << 24
            | (bytes[1].0 as u32) << 18
            | (bytes[2].0 as u32) << 12
            | (bytes[3].0 as u32) << 6
            | (bytes[4].0 as u32);

        Word(signbit | value)
    }

    /// Converts a [`Word`] to its sign/bytes representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, word, num::Sign};
    ///
    /// let sign = Sign::Minus;
    /// let bytes = [byte!(1), byte!(2), byte!(3), byte!(4), byte!(5)];
    ///
    /// assert_eq!(
    ///     word![-, 1, 2, 3, 4, 5].to_sign_bytes(),
    ///     (sign, bytes)
    /// );
    /// ```
    pub const fn to_sign_bytes(self) -> (Sign, [Byte; 5]) {
        (self.sign(), self.bytes())
    }

    /// Returns the sign of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Sign, Word}};
    ///
    /// assert_eq!(word!(10).sign(), Sign::Plus);
    /// assert_eq!(word!(-10).sign(), Sign::Minus);
    /// assert_eq!(Word::POS_ZERO.sign(), Sign::Plus);
    /// assert_eq!(Word::NEG_ZERO.sign(), Sign::Minus);
    /// assert_eq!(Word::MAX.sign(), Sign::Plus);
    /// assert_eq!(Word::MIN.sign(), Sign::Minus);
    /// ```
    pub const fn sign(self) -> Sign {
        unsafe { transmute(((self.mask_sign()) >> 30) as u8) }
    }

    /// Returns the magnitude of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Word};
    ///
    /// assert_eq!(word!(10).magnitude(), 10);
    /// assert_eq!(word!(10).magnitude(), 10);
    /// assert_eq!(Word::MAX.magnitude(), (1 << 30) - 1);
    /// assert_eq!(Word::MIN.magnitude(), (1 << 30) - 1);
    /// assert_eq!(Word::POS_ZERO.magnitude(), 0);
    /// assert_eq!(Word::NEG_ZERO.magnitude(), 0);
    /// ```
    pub const fn magnitude(self) -> u32 {
        self.mask_value()
    }

    /// Return the bytes of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, word};
    ///
    /// assert_eq!(
    ///     word![-, 1, 2, 3, 4, 5].bytes(),
    ///     [byte!(1), byte!(2), byte!(3), byte!(4), byte!(5)
    /// ]);
    /// ```
    pub const fn bytes(self) -> [Byte; 5] {
        [
            Byte((self.0 >> 24) as u8 & Byte::VALUE_MASK),
            Byte((self.0 >> 18) as u8 & Byte::VALUE_MASK),
            Byte((self.0 >> 12) as u8 & Byte::VALUE_MASK),
            Byte((self.0 >> 6) as u8 & Byte::VALUE_MASK),
            Byte(self.0 as u8 & Byte::VALUE_MASK),
        ]
    }

    /// Returns `true` if `self` is positive or negative zero and `false`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Word};
    ///
    /// // Positive
    /// assert!(!Word::MAX.is_zero());
    /// assert!(!word!(10).is_zero());
    ///
    /// // Negative
    /// assert!(!Word::MIN.is_zero());
    /// assert!(!word!(-10).is_zero());
    ///
    /// // Zero
    /// assert!(Word::POS_ZERO.is_zero());
    /// assert!(Word::NEG_ZERO.is_zero());
    /// ```
    pub const fn is_zero(self) -> bool {
        self.mask_value() == 0
    }

    /// Returns `true` if `self` is positive and false if `self` is zero or
    /// negative.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Word};
    ///
    /// // Positive
    /// assert!(Word::MAX.is_positive());
    /// assert!(word!(10).is_positive());
    ///
    /// // Negative
    /// assert!(!Word::MIN.is_positive());
    /// assert!(!word!(-10).is_positive());
    ///
    /// // Zero
    /// assert!(!Word::POS_ZERO.is_positive());
    /// assert!(!Word::NEG_ZERO.is_positive());
    /// ```
    pub const fn is_positive(self) -> bool {
        self.mask_sign() == 0 && self.mask_value() != 0
    }

    /// Returns `true` if `self` is negative and false if `self` is zero or
    /// positive.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Word};
    ///
    /// // Positive
    /// assert!(!Word::MAX.is_negative());
    /// assert!(!word!(10).is_negative());
    ///
    /// // Negative
    /// assert!(Word::MIN.is_negative());
    /// assert!(word!(-10).is_negative());
    ///
    /// // Zero
    /// assert!(!Word::POS_ZERO.is_negative());
    /// assert!(!Word::NEG_ZERO.is_negative());
    /// ```
    pub const fn is_negative(self) -> bool {
        self.mask_sign() != 0 && self.mask_value() != 0
    }

    pub const fn is_even(self) -> bool {
        self.0 & 1 == 0
    }

    /// Compute the absolute value of `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Sign};
    ///
    /// assert_eq!(word!(1).abs(), word!(1));
    /// assert_eq!(word!(-1).abs(), word!(1));
    /// assert_eq!(word!(-0).abs().sign(), Sign::Plus);
    /// ```
    pub const fn abs(self) -> Word {
        Self(self.mask_value())
    }

    /// Checked addition. Computes `self + rhs`, returning `None` if overflow
    /// occurred.
    ///
    /// The sign of `self` is retained if the result is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Word, Sign}};
    ///
    /// assert_eq!(word!(1).checked_add(word!(2)), Some(word!(3)));
    /// assert_eq!(Word::MAX.checked_add(word!(1)), None);
    /// assert_eq!(word!(1).checked_add(word!(-1)).unwrap().sign(), Sign::Plus);
    /// assert_eq!(word!(-1).checked_add(word!(1)).unwrap().sign(), Sign::Minus);
    /// ```
    pub const fn checked_add(self, rhs: Word) -> Option<Word> {
        let (res, overflow) = self.overflowing_add(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Checked subtraction. Computes `self - rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// The sign of `self` is retained if the result is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::{Word, Sign}};
    ///
    /// assert_eq!(word!(3).checked_sub(word!(2)), Some(word!(1)));
    /// assert_eq!(Word::MIN.checked_sub(word!(1)), None);
    /// assert_eq!(word!(1).checked_sub(word!(1)).unwrap().sign(), Sign::Plus);
    /// assert_eq!(word!(-1).checked_sub(word!(-1)).unwrap().sign(), Sign::Minus);
    /// ```
    pub const fn checked_sub(self, rhs: Word) -> Option<Word> {
        let (res, overflow) = self.overflowing_sub(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Checked multiplication. Computes `self * rhs`, returning `None` if
    /// overflow occurred.
    ///
    /// The sign of the result is `self.sign() * rhs.sign()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, num::Word};
    ///
    /// assert_eq!(word!(1).checked_mul(word!(-1)), Some(word!(-1)));
    /// assert_eq!(word!(2).checked_mul(word!(3)), Some(word!(6)));
    /// assert_eq!(Word::MAX.checked_mul(word!(2)), None);
    /// ```
    pub const fn checked_mul(self, rhs: Word) -> Option<Word> {
        let (res, overflow) = self.overflowing_mul(rhs);
        if overflow { None } else { Some(res) }
    }

    /// Overflowing addition. Computes `self + rhs`, returning the value and
    /// carry.
    ///
    /// If the result is zero, the sign of `self` is retained.
    pub const fn overflowing_add(self, rhs: Word) -> (Word, bool) {
        let lhs_value = self.mask_value();
        let lhs_sign = self.mask_sign();
        let rhs_value = rhs.mask_value();
        let rhs_sign = rhs.mask_sign();

        if lhs_sign == rhs_sign {
            let added = lhs_value + rhs_value;
            let res_value = added & Word::VALUE_MASK;
            let overflow = added > Word::VALUE_MASK;

            (Word(lhs_sign | res_value), overflow)
        } else if lhs_value >= rhs_value {
            // Propogates sign of `self` on zero.
            (Word(lhs_sign | (lhs_value - rhs_value)), false)
        } else {
            (Word(rhs_sign | (rhs_value - lhs_value)), false)
        }
    }

    /// Overflowing subtraction. Computes `self + rhs`, returning the value
    /// and carry.
    ///
    /// If the result is zero, the sign of `self` is retained.
    pub const fn overflowing_sub(self, rhs: Word) -> (Word, bool) {
        self.overflowing_add(rhs.const_neg())
    }

    /// Overflowing multiplication. Computes `self * rhs`, returning the value
    /// and wether an overflow occurred.
    ///
    /// The sign of the result is `self.sign() * rhs.sign()`.
    pub const fn overflowing_mul(self, rhs: Word) -> (Word, bool) {
        let res_sign = self.mask_sign() ^ rhs.mask_sign();

        // Must promote to u64 to fit 60 bits.
        let mulled = self.mask_value() as u64 * rhs.mask_value() as u64;
        let res_value = mulled as u32 & Self::VALUE_MASK;
        let overflow = mulled > Self::VALUE_MASK as u64;

        (Word(res_sign | res_value), overflow)
    }

    /// Returns the value of `self` as if loaded from memory by a MIX machine
    /// with the valid field specification `field`, or returns `None` for an
    /// invalid field specification.
    ///
    /// Valid field specifications are bytes F &equals; 8L &plus; R where
    /// 0 &le; L &le; R &le; 5.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{byte, word, num::Byte};
    ///
    /// // (2:4) = 8 * 2 + 4 = 20
    /// let field = byte!(20);
    /// let value = word![-, 1, 2, 3, 4, 5];
    ///
    /// assert_eq!(value.with_load(field), Some(word![+, 0, 0, 2, 3, 4]));
    /// assert_eq!(value.with_load(Byte::MAX), None);
    /// ```
    pub const fn with_load(self, field_spec: FieldSpec) -> Word {
        let masks = field_spec.masks();
        let sign_bit =
            if field_spec.includes_sign() { self.mask_sign() } else { 0 };
        let value_bits = (self.0 & masks.bit_mask) >> masks.bit_offset;

        Word(sign_bit | value_bits)
    }

    /// Returns the value of `self` as if the value of `value` has been stored
    /// over it with the valid field specification `field`, or returns `None`
    /// for an invalid field specification.
    ///
    /// Valid field specifications are bytes F &equals; 8L &plus; R where
    /// 0 &le; L &le; R &le; 5.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::{word, byte, num::Byte};
    ///
    /// let dest = word![+, 1, 2, 3, 4, 5];
    /// let value = word![-, 6, 7, 8, 9, 10];
    ///
    /// // (0:3) = 8 * 0 + 3 = 3
    /// let field = byte!(3);
    ///
    /// assert_eq!(dest.with_store(value, field), Some(word![-, 8, 9, 10, 4, 5]));
    /// assert_eq!(dest.with_store(value, Byte::MAX), None);
    /// ```
    pub const fn with_store(self, value: Word, field_spec: FieldSpec) -> Word {
        let masks = field_spec.masks();
        let sign_bit = if field_spec.includes_sign() {
            value.mask_sign()
        } else {
            self.mask_sign()
        };

        let new_value_bits =
            (value.mask_value() << masks.bit_offset) & masks.bit_mask;

        let old_value_bits = self.mask_value() & !masks.bit_mask;

        Word(sign_bit | new_value_bits | old_value_bits)
    }

    /// Returns `self` as though its (0:2) field has been set by `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::word;
    ///
    /// assert_eq!(
    ///     word![+, 1, 2, 3, 4, 5].with_address(word![-, 6, 7, 8, 9, 10]),
    ///     word![-, 9, 10, 3, 4, 5]
    /// );
    /// ```
    pub const fn with_address(self, value: Word) -> Word {
        let sign_bit = value.mask_sign();
        let high_two_bytes = (value.0 & ((1 << 12) - 1)) << 18;
        let low_three_bytes = self.0 & ((1 << 18) - 1);

        Word(sign_bit | high_two_bytes | low_three_bytes)
    }

    /// Returns `self` as though its (3:3) field has been set by `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::word;
    ///
    /// assert_eq!(
    ///     word![+, 1, 2, 3, 4, 5].with_index(word![-, 6, 7, 8, 9, 10]),
    ///     word![+, 1, 2, 10, 4, 5]
    /// );
    /// ```
    pub const fn with_index(self, value: Word) -> Word {
        let third_byte = (value.0 & ((1 << 6) - 1)) << 12;
        let other_bytes = self.0 & (((1 << 31) - 1) & !(0x3F << 12));

        Word(third_byte | other_bytes)
    }

    /// Returns `self` as though its (4:4) field has been set by `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::word;
    ///
    /// assert_eq!(
    ///     word![+, 1, 2, 3, 4, 5].with_field(word![-, 6, 7, 8, 9, 10]),
    ///     word![+, 1, 2, 3, 10, 5]
    /// );
    /// ```
    pub const fn with_field(self, value: Word) -> Word {
        let fourth_byte = (value.0 & ((1 << 6) - 1)) << 6;
        let other_bytes = self.0 & (((1 << 31) - 1) & !(0x3F << 6));

        Word(fourth_byte | other_bytes)
    }

    /// Returns `self` as though its (5:5) field has been set by `value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::word;
    ///
    /// assert_eq!(
    ///     word![+, 1, 2, 3, 4, 5].with_opcode(word![-, 6, 7, 8, 9, 10]),
    ///     word![+, 1, 2, 3, 4, 10]
    /// );
    /// ```
    pub const fn with_opcode(self, value: Word) -> Word {
        const BYTE_MASK: u32 = Byte::VALUE_MASK as u32;

        let fifth_byte = value.0 & BYTE_MASK;
        let other_bytes = self.0 & (Word::MASK & !BYTE_MASK);

        Word(fifth_byte | other_bytes)
    }

    pub const fn with_sign(self, sign: Sign) -> Word {
        let sign_bit = (sign as u32) << 30;
        let value_bits = self.mask_value();
        Word(sign_bit | value_bits)
    }

    const SIGN_MASK: u32 = 1 << 30;
    const VALUE_MASK: u32 = (1 << 30) - 1;
    const MASK: u32 = Self::SIGN_MASK | Self::VALUE_MASK;

    const fn mask_sign(self) -> u32 {
        self.0 & Word::SIGN_MASK
    }

    const fn mask_value(self) -> u32 {
        self.0 & Word::VALUE_MASK
    }

    const fn const_neg(self) -> Word {
        Word(self.0 ^ Word::SIGN_MASK)
    }

    pub(crate) const fn truncate_to_short(self) -> Short {
        let sign_bit = (self.mask_sign() >> 18) as u16;
        let value_bits = (self.0 as u16) & Short::VALUE_MASK;

        Short(sign_bit | value_bits)
    }
}

impl Neg for Word {
    type Output = Word;

    fn neg(self) -> Self::Output {
        self.const_neg()
    }
}

impl PartialEq for Word {
    fn eq(&self, other: &Self) -> bool {
        self.to_i32() == other.to_i32()
    }
}

impl Eq for Word {}

impl PartialOrd for Word {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Word {
    fn cmp(&self, other: &Self) -> Ordering {
        self.to_i32().cmp(&other.to_i32())
    }
}

impl Hash for Word {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_i32().hash(state);
    }
}

impl fmt::Display for Word {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad_integral(
            self.mask_sign() == 0,
            "",
            &self.mask_value().to_string(),
        )
    }
}

impl Encode for Word {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.0.encode(w)
    }
}

impl Decode for Word {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        let repr = u32::decode(r)?;
        if repr & !Word::MASK == 0 {
            Ok(Word(repr))
        } else {
            Err(io::Error::other(EncodingError))
        }
    }
}

/// A MIX memory address.
///
/// Represents all valid MIX addresses: 0 to 3999.
#[repr(transparent)]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Default, Hash,
)]
pub struct MemoryAddress(u16);

impl MemoryAddress {
    /// The minimum memory address. Equal to 0.
    pub const MIN: MemoryAddress = MemoryAddress(0);

    /// The maximum memory address. Equal to 3999.
    pub const MAX: MemoryAddress = MemoryAddress(3999);

    /// Converts a [`MemoryAddress`] to `u16`.
    pub const fn to_u16(self) -> u16 {
        self.0
    }

    /// Converts a `u16` to [`MemoryAddress`].
    pub const fn from_u16(value: u16) -> Option<MemoryAddress> {
        if value <= MemoryAddress::MAX.0 {
            Some(MemoryAddress(value))
        } else {
            None
        }
    }

    /// Converts an `u16` to a [`MemoryAddress`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value >
    /// MemoryAddress::MAX.to_u16()`.
    pub const unsafe fn from_u16_unchecked(value: u16) -> MemoryAddress {
        debug_assert!(value <= MemoryAddress::MAX.0);
        MemoryAddress(value)
    }
}

impl fmt::Display for MemoryAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Encode for MemoryAddress {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.0.encode(w)
    }
}

impl Decode for MemoryAddress {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        MemoryAddress::from_u16(u16::decode(r)?)
            .ok_or_else(|| io::Error::other(EncodingError))
    }
}

/// A MIX location counter.
///
/// This represents the location counter &circledast; used in Knuth's
/// description of the MIX assembly process. It is essentially an unsigned two
/// byte MIX number. It is used often to represent values that can potentially
/// be memory addresses, but not always.
#[repr(transparent)]
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Default, Hash,
)]
pub struct LocationCounter(u16);

impl LocationCounter {
    /// The smallest value that can be represented by [`LocationCounter`].
    /// Equal to 0.
    pub const MIN: LocationCounter = LocationCounter(0);

    /// The largest value that can be represented by [`LocationCounter`]. Equal
    /// to (2<sup>12</sup> &minus; 1).
    pub const MAX: LocationCounter = LocationCounter((1 << 12) - 1);

    /// Converts a [`MemoryAddress`] to `u16`.
    pub const fn to_u16(self) -> u16 {
        self.0
    }

    /// Converts a `u16` to [`MemoryAddress`].
    pub const fn from_u16(value: u16) -> Option<LocationCounter> {
        if value <= LocationCounter::MAX.0 {
            Some(LocationCounter(value))
        } else {
            None
        }
    }

    /// Converts an `u16` to a [`LocationCounter`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value >
    /// LocationCounter::MAX.to_u16()`.
    pub const unsafe fn from_u16_unchecked(value: u16) -> LocationCounter {
        debug_assert!(value <= LocationCounter::MAX.0);
        LocationCounter(value)
    }

    pub const fn location_after(address: MemoryAddress) -> LocationCounter {
        // SAFETY: MemoryAddress::MAX + 1 = 4000 < 4095 = LocationCounter::MAX
        unsafe { LocationCounter::from_u16_unchecked(address.to_u16() + 1) }
    }
}

impl fmt::Display for LocationCounter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Encode for LocationCounter {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.0.encode(w)
    }
}

impl Decode for LocationCounter {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        LocationCounter::from_u16(u16::decode(r)?)
            .ok_or_else(|| io::Error::other(EncodingError))
    }
}

#[derive(Debug, Clone, Copy)]
struct FieldSpecMasks {
    bit_mask: u32,
    bit_offset: u8,
}

/// Lookup table for valid field specs.
const FIELD_SPEC_MASKS: [Option<FieldSpecMasks>; 64] = {
    let mut field_info = [None; 64];

    let mut left = 0;
    while left < 8 {
        let mut right = 0;
        while right < 8 {
            let index = left << 3 | right;
            if left <= right && right <= 5 {
                let byte_left = if left == 0 { 1 } else { left };
                let byte_right = if right == 0 { 1 } else { right + 1 };

                let bit_width = (byte_right - byte_left) * 6;
                let bit_offset = (6 - byte_right) * 6;
                let bit_mask = ((1 << bit_width) - 1) << bit_offset;

                field_info[index] = Some(FieldSpecMasks {
                    bit_mask,
                    bit_offset: bit_offset as u8,
                });
            }

            right += 1;
        }
        left += 1;
    }

    field_info
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InvalidFieldSpecError(());

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FieldSpec {
    byte: u8,
}

impl FieldSpec {
    pub const fn from_parts(left: u8, right: u8) -> Option<Self> {
        if left <= right && right <= 5 {
            Some(FieldSpec { byte: left << 3 | right })
        } else {
            None
        }
    }

    pub const fn includes_sign(self) -> bool {
        self.byte < 8
    }

    pub const fn to_byte(self) -> Byte {
        Byte(self.byte)
    }

    pub const fn from_byte(value: Byte) -> Option<Self> {
        Self::from_parts(value.0 >> 3, value.0 & 0b111)
    }

    const fn masks(self) -> FieldSpecMasks {
        unsafe { FIELD_SPEC_MASKS[self.byte as usize].unwrap_unchecked() }
    }
}

impl From<FieldSpec> for Byte {
    fn from(value: FieldSpec) -> Self {
        value.to_byte()
    }
}

impl TryFrom<Byte> for FieldSpec {
    type Error = InvalidFieldSpecError;

    fn try_from(value: Byte) -> Result<Self, Self::Error> {
        Self::from_byte(value).ok_or(InvalidFieldSpecError(()))
    }
}
