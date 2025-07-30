//! MIX numerics.
//!
//! Includes fundamental MIX numeric types like [`Word`], and [`Byte`]. All
//! types are implemented with the assumption that bytes are 6 bits, though
//! not all MIX systems have this.

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::fmt::Write;
use std::hash::Hash;
use std::hash::Hasher;
use std::mem::transmute;
use std::ops::Neg;

/// Enumeration representing numeric signs.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sign {
    /// Plus sign `+`.
    Plus = 0,
    /// Minus sign `-`.
    Minus = 1,
}

impl Neg for Sign {
    type Output = Sign;

    fn neg(self) -> Self::Output {
        unsafe { transmute(1 - self as u8) }
    }
}

impl fmt::Display for Sign {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_char(if *self == Sign::Plus { '+' } else { '-' })
    }
}

/// An error that can be returned when converting to between integral types.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TryFromIntError(());

impl fmt::Display for TryFromIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("out of range integral type conversion")
    }
}

impl Error for TryFromIntError {}

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

    /// Convert `self` to the smallest fitting normal integer type, `i16`.
    /// Negative zero is mapped to zero.
    pub const fn to_u8(self) -> u8 {
        self.0
    }

    /// Converts an `u8` to a [`Byte`] without checking whether it is valid.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value.abs() >
    /// Byte::MAX.to_u8()`.
    pub const unsafe fn from_u8_unchecked(value: u8) -> Byte {
        debug_assert!(value <= Byte::VALUE_MASK);
        Byte(value)
    }

    /// Mask for the u8 representation of the byte.
    const VALUE_MASK: u8 = (1 << 6) - 1;
}

impl fmt::Display for Byte {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{}", self.0))
    }
}

/// A MIX short integer.
///
/// We say a `short` is the two byte integers often used in MIX index
/// registers, jump registers, and the instruction address parameter.
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

    /// Convert `self` to the smallest fitting normal integer type, `i16`.
    ///
    /// Negative zero is mapped to zero.
    pub const fn to_i16(self) -> i16 {
        if self.mask_sign() == 0 {
            self.0 as i16
        } else {
            -(self.mask_value() as i16)
        }
    }

    /// Converts an `i16` to a [`Short`] without checking whether it is valid.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value.abs() >
    /// Short::MAX.to_i16()`.
    pub const unsafe fn from_i16_unchecked(value: i16) -> Short {
        debug_assert!(value.unsigned_abs() <= Short::VALUE_MASK);

        if value >= 0 {
            Short(value as u16)
        } else {
            Short(-value as u16 | Short::SIGN_MASK)
        }
    }

    /// Converts the sign/bytes representation of a short into a [`Short`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Short};
    ///
    /// let sign = Sign::Minus;
    /// let bytes = [0b101101, 0b111101].map(|v| Byte::try_from(v).unwrap());
    ///
    /// assert_eq!(
    ///     Short::from_sign_and_bytes(sign, bytes),
    ///     Short::try_from(-0b101101111101).unwrap()
    /// );
    /// ```
    pub const fn from_sign_and_bytes(sign: Sign, bytes: [Byte; 2]) -> Short {
        let signbit = (sign as u16) << 12;
        let value = (bytes[0].0 as u16) << 6 | bytes[1].0 as u16;

        Short(signbit | value)
    }

    /// Converts `self` to its sign/bytes representation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Short};
    ///
    /// let value = Short::try_from(-0b101101111101).unwrap();
    /// let sign = Sign::Minus;
    /// let bytes = [
    ///     Byte::try_from(0b101101).unwrap(),
    ///     Byte::try_from(0b111101).unwrap()
    /// ];
    ///
    /// assert_eq!(value.to_sign_and_bytes(), (sign, bytes));
    /// ```
    pub const fn to_sign_and_bytes(self) -> (Sign, [Byte; 2]) {
        (self.sign(), self.bytes())
    }

    /// Returns the sign of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Short};
    ///
    /// assert_eq!(Short::MAX.sign(), Sign::Plus);
    /// assert_eq!(Short::MIN.sign(), Sign::Minus);
    /// assert_eq!(Short::POS_ZERO.sign(), Sign::Plus);
    /// assert_eq!(Short::NEG_ZERO.sign(), Sign::Minus);
    /// assert_eq!(Short::try_from(10).unwrap().sign(), Sign::Plus);
    /// assert_eq!(Short::try_from(-10).unwrap().sign(), Sign::Minus);
    /// ```
    pub const fn sign(self) -> Sign {
        unsafe { transmute(((self.mask_sign()) >> 12) as u8) }
    }

    /// Return the bytes of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Byte, Short};
    ///
    /// let value = Short::try_from(-0b101101111101).unwrap();
    /// let bytes = [
    ///     Byte::try_from(0b101101).unwrap(),
    ///     Byte::try_from(0b111101).unwrap()
    /// ];
    ///
    /// assert_eq!(value.bytes(), bytes);
    /// ```
    pub const fn bytes(self) -> [Byte; 2] {
        let v = self.mask_value();
        [Byte((v >> 6) as u8), Byte(v as u8 & Byte::VALUE_MASK)]
    }

    /// Returns `true` if `self` is positive or negative zero and `false`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Short;
    ///
    /// // Positive
    /// assert!(!Short::MAX.is_zero());
    /// assert!(!Short::try_from(10).unwrap().is_zero());
    ///
    /// // Negative
    /// assert!(!Short::MIN.is_zero());
    /// assert!(!Short::try_from(-10).unwrap().is_zero());
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
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Short;
    ///
    /// // Positive
    /// assert!(Short::MAX.is_positive());
    /// assert!(Short::try_from(10).unwrap().is_positive());
    ///
    /// // Negative
    /// assert!(!Short::MIN.is_positive());
    /// assert!(!Short::try_from(-10).unwrap().is_positive());
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
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Short;
    ///
    /// // Positive
    /// assert!(!Short::MAX.is_negative());
    /// assert!(!Short::try_from(10).unwrap().is_negative());
    ///
    /// // Negative
    /// assert!(Short::MIN.is_negative());
    /// assert!(Short::try_from(-10).unwrap().is_negative());
    ///
    /// // Zero
    /// assert!(!Short::POS_ZERO.is_negative());
    /// assert!(!Short::NEG_ZERO.is_negative());
    /// ```
    pub const fn is_negative(self) -> bool {
        self.mask_sign() != 0 && self.mask_value() != 0
    }

    /// Compute the absolute value of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Short;
    ///
    /// let one = Short::try_from(1).unwrap();
    /// let neg_one = Short::try_from(-1).unwrap();
    ///
    /// assert_eq!(one.abs(), one);
    /// assert_eq!(neg_one.abs(), one);
    /// ```
    pub const fn abs(self) -> Short {
        Short(self.mask_value())
    }

    const SIGN_MASK: u16 = 1 << 12;
    const VALUE_MASK: u16 = (1 << 12) - 1;

    const fn mask_sign(self) -> u16 {
        self.0 & Short::SIGN_MASK
    }

    const fn mask_value(self) -> u16 {
        self.0 & Short::VALUE_MASK
    }
}

impl Neg for Short {
    type Output = Short;

    fn neg(self) -> Self::Output {
        Short(self.0 ^ Short::SIGN_MASK)
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
        f.write_fmt(format_args!("{}{}", self.sign(), self.mask_value()))
    }
}

#[derive(Clone, Copy)]
struct WordFieldInfo {
    invalid: bool,
    bit_mask: u32,
    bit_offset: u8,
}

/// Lookup table for storing and loading operations.
const WORD_FIELD_INFO: [WordFieldInfo; 64] = {
    let mut field_info =
        [WordFieldInfo { invalid: false, bit_mask: 0, bit_offset: 0 }; 64];

    let mut left = 0;
    while left < 8 {
        let mut right = 0;
        while right < 8 {
            let index = left << 3 | right;

            if left > right || right > 5 {
                field_info[index].invalid = true;
            } else {
                let byte_left = if left == 0 { 1 } else { left };
                let byte_right = if right == 0 { 1 } else { right + 1 };

                let bit_width = (byte_right - byte_left) * 6;
                let bit_offset = (6 - byte_right) * 6;
                let bit_mask = ((1 << bit_width) - 1) << bit_offset;

                field_info[index].bit_mask = bit_mask;
                field_info[index].bit_offset = bit_offset as u8;
            }

            right += 1;
        }
        left += 1;
    }

    field_info
};

/// A MIX word.
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

    /// Convert `self` to the smallest fitting normal integer type, `i32`.
    /// Negative zero is mapped to zero.
    pub const fn to_i32(self) -> i32 {
        if self.mask_sign() == 0 {
            self.0 as i32
        } else {
            -(self.mask_value() as i32)
        }
    }

    /// Converts an `i32` to a [`Word`] without checking whether it is valid.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value.abs() >
    /// Word::MAX.to_i32()`.
    pub const unsafe fn from_i32_unchecked(value: i32) -> Word {
        debug_assert!(value.unsigned_abs() <= Word::VALUE_MASK);

        if value >= 0 {
            Word(value as u32)
        } else {
            Word(-value as u32 | Word::SIGN_MASK)
        }
    }

    /// Converts the sign/bytes representation of a word into a [`Word`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let sign = Sign::Minus;
    /// let bytes = [0b100110, 0b010100, 0b000010, 0b101001, 0b111111]
    ///     .map(|v| Byte::try_from(v).unwrap());
    ///
    /// assert_eq!(
    ///     Word::from_sign_and_bytes(sign, bytes),
    ///     Word::try_from(-0b100110010100000010101001111111).unwrap()
    /// );
    /// ```
    pub const fn from_sign_and_bytes(sign: Sign, bytes: [Byte; 5]) -> Word {
        let signbit = (sign as u32) << 30;
        let value = (bytes[0].0 as u32) << 24
            | (bytes[1].0 as u32) << 18
            | (bytes[2].0 as u32) << 12
            | (bytes[3].0 as u32) << 6
            | (bytes[4].0 as u32);

        Word(signbit | value)
    }

    /// Converts `self` to its sign/bytes representation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let value = Word::try_from(-0b100110010100000010101001111111).unwrap();
    /// let sign = Sign::Minus;
    /// let bytes = [
    ///     Byte::try_from(0b100110).unwrap(),
    ///     Byte::try_from(0b010100).unwrap(),
    ///     Byte::try_from(0b000010).unwrap(),
    ///     Byte::try_from(0b101001).unwrap(),
    ///     Byte::try_from(0b111111).unwrap(),
    /// ];
    ///
    /// assert_eq!(value.to_sign_and_bytes(), (sign, bytes));
    /// ```
    pub const fn to_sign_and_bytes(self) -> (Sign, [Byte; 5]) {
        (self.sign(), self.bytes())
    }

    /// Returns the sign of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Word};
    ///
    /// assert_eq!(Word::MAX.sign(), Sign::Plus);
    /// assert_eq!(Word::MIN.sign(), Sign::Minus);
    /// assert_eq!(Word::POS_ZERO.sign(), Sign::Plus);
    /// assert_eq!(Word::NEG_ZERO.sign(), Sign::Minus);
    /// assert_eq!(Word::try_from(10).unwrap().sign(), Sign::Plus);
    /// assert_eq!(Word::try_from(-10).unwrap().sign(), Sign::Minus);
    /// ```
    pub const fn sign(self) -> Sign {
        unsafe { transmute(((self.mask_sign()) >> 30) as u8) }
    }

    /// Return the bytes of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Byte, Word};
    ///
    /// let value = Word::try_from(-0b100110010100000010101001111111).unwrap();
    /// let bytes = [
    ///     Byte::try_from(0b100110).unwrap(),
    ///     Byte::try_from(0b010100).unwrap(),
    ///     Byte::try_from(0b000010).unwrap(),
    ///     Byte::try_from(0b101001).unwrap(),
    ///     Byte::try_from(0b111111).unwrap(),
    /// ];
    ///
    /// assert_eq!(value.bytes(), bytes);
    /// ```
    pub const fn bytes(self) -> [Byte; 5] {
        let v = self.mask_value();
        [
            Byte((v >> 24) as u8),
            Byte((v >> 18) as u8 & Byte::VALUE_MASK),
            Byte((v >> 12) as u8 & Byte::VALUE_MASK),
            Byte((v >> 6) as u8 & Byte::VALUE_MASK),
            Byte(v as u8 & Byte::VALUE_MASK),
        ]
    }

    /// Returns `true` if `self` is positive or negative zero and `false`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// // Positive
    /// assert!(!Word::MAX.is_zero());
    /// assert!(!Word::try_from(10).unwrap().is_zero());
    ///
    /// // Negative
    /// assert!(!Word::MIN.is_zero());
    /// assert!(!Word::try_from(-10).unwrap().is_zero());
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
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// // Positive
    /// assert!(Word::MAX.is_positive());
    /// assert!(Word::try_from(10).unwrap().is_positive());
    ///
    /// // Negative
    /// assert!(!Word::MIN.is_positive());
    /// assert!(!Word::try_from(-10).unwrap().is_positive());
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
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// // Positive
    /// assert!(!Word::MAX.is_negative());
    /// assert!(!Word::try_from(10).unwrap().is_negative());
    ///
    /// // Negative
    /// assert!(Word::MIN.is_negative());
    /// assert!(Word::try_from(-10).unwrap().is_negative());
    ///
    /// // Zero
    /// assert!(!Word::POS_ZERO.is_negative());
    /// assert!(!Word::NEG_ZERO.is_negative());
    /// ```
    pub const fn is_negative(self) -> bool {
        self.mask_sign() != 0 && self.mask_value() != 0
    }

    /// Compute the absolute value of `self`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let one = Word::try_from(1).unwrap();
    /// let neg_one = Word::try_from(-1).unwrap();
    ///
    /// assert_eq!(one.abs(), one);
    /// assert_eq!(neg_one.abs(), one);
    /// ```
    pub const fn abs(self) -> Word {
        Self(self.mask_value())
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
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let value = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
    /// let field = Byte::try_from(8 * 2 + 4).unwrap();
    /// let expected = make_word(Sign::Plus, [0, 0, 2, 3, 4]);
    ///
    /// assert_eq!(value.load(field), Some(expected));
    /// ```
    ///
    /// Invalid field specification:
    ///
    /// ```
    /// use mixlib::num::{Byte, Word};
    ///
    /// assert_eq!(Word::default().load(Byte::MAX), None);
    /// ```
    pub const fn load(self, field: Byte) -> Option<Word> {
        let field = field.to_u8();
        let info = WORD_FIELD_INFO[field as usize];

        if info.invalid {
            return None;
        }

        let signbit = if field < 8 { self.mask_sign() } else { 0 };
        let uvalue = (self.mask_value() & info.bit_mask) >> info.bit_offset;

        Some(Word(signbit | uvalue))
    }

    /// Returns the value of `dest` as if the value of `self` has been stored
    /// over it with the valid field specification `field`, or returns `None`
    /// for an invalid field specification.
    ///
    /// Valid field specifications are bytes F &equals; 8L &plus; R where
    /// 0 &le; L &le; R &le; 5.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let value = make_word(Sign::Minus, [1, 2, 3, 4, 5]);
    /// let dest = make_word(Sign::Plus, [6, 7, 8, 9, 0]);
    /// let field = Byte::try_from(8 * 0 + 3).unwrap();
    /// let expected = make_word(Sign::Minus, [3, 4, 5, 9, 0]);
    ///
    /// assert_eq!(value.store(dest, field), Some(expected));
    /// ```
    ///
    /// Invalid field specification:
    ///
    /// ```
    /// use mixlib::num::{Byte, Word};
    ///
    /// assert_eq!(Word::default().store(Word::default(), Byte::MAX), None);
    /// ```
    pub const fn store(self, dest: Word, field: Byte) -> Option<Word> {
        let field = field.to_u8();
        let info = WORD_FIELD_INFO[field as usize];

        if info.invalid {
            return None;
        }

        let signbit =
            if field < 8 { self.mask_sign() } else { dest.mask_sign() };

        let overwrite = (self.mask_value() << info.bit_offset) & info.bit_mask;
        let uvalue = overwrite | (dest.mask_value() & !info.bit_mask);

        Some(Word(signbit | uvalue))
    }

    /// Returns `self` as though its (0:2) field has been set by `value`.
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let value = make_word(Sign::Plus, [0, 1, 2, 3, 4]);
    /// let new_address = make_word(Sign::Minus, [5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(
    ///     value.with_address(new_address),
    ///     make_word(Sign::Minus, [8, 9, 2, 3, 4])
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
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let value = make_word(Sign::Plus, [0, 1, 2, 3, 4]);
    /// let new_index = make_word(Sign::Minus, [5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(
    ///     value.with_index(new_index),
    ///     make_word(Sign::Plus, [0, 1, 9, 3, 4])
    /// );
    /// ```
    pub const fn with_index(self, value: Word) -> Word {
        let third_byte = (value.0 & ((1 << 8) - 1)) << 12;
        let other_bytes = self.0 & (((1 << 31) - 1) & !(0x3F << 12));

        Word(third_byte | other_bytes)
    }

    /// Returns `self` as though its (4:4) field has been set by `value`.
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let value = make_word(Sign::Plus, [0, 1, 2, 3, 4]);
    /// let new_field = make_word(Sign::Minus, [5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(
    ///     value.with_field(new_field),
    ///     make_word(Sign::Plus, [0, 1, 2, 9, 4])
    /// );
    /// ```
    pub const fn with_field(self, value: Word) -> Word {
        let fourth_byte = (value.0 & ((1 << 8) - 1)) << 6;
        let other_bytes = self.0 & (((1 << 31) - 1) & !(0x3F << 6));

        Word(fourth_byte | other_bytes)
    }

    /// Returns `self` as though its (5:5) field has been set by `value`.
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let value = make_word(Sign::Plus, [0, 1, 2, 3, 4]);
    /// let new_opcode = make_word(Sign::Minus, [5, 6, 7, 8, 9]);
    ///
    /// assert_eq!(
    ///     value.with_opcode(new_opcode),
    ///     make_word(Sign::Plus, [0, 1, 2, 3, 9])
    /// );
    /// ```
    pub const fn with_opcode(self, value: Word) -> Word {
        let fifth_byte = value.0 & ((1 << 8) - 1);
        let other_bytes = self.0 & (((1 << 31) - 1) & !0x3F);

        Word(fifth_byte | other_bytes)
    }

    /// Stores `value` at `self`'s (0:2) field. Equivalent to
    /// `*self = self.with_address(value)`.
    pub const fn set_address(&mut self, value: Word) {
        *self = self.with_address(value);
    }

    /// Stores `value` at `self`'s (3:3) field. Equivalent to
    /// `*self = self.with_index(value)`.
    pub const fn set_index(&mut self, value: Word) {
        *self = self.with_index(value);
    }

    /// Stores `value` at `self`'s (4:4) field. Equivalent to
    /// `*self = self.with_field(value)`.
    pub const fn set_field(&mut self, value: Word) {
        *self = self.with_field(value);
    }

    /// Stores `value` at `self`'s (5:5) field. Equivalent to
    /// `*self = self.with_opcode(value)`.
    pub const fn set_opcode(&mut self, value: Word) {
        *self = self.with_opcode(value);
    }

    /// MIX addition.
    ///
    /// This behaves in the manner of the MIX `ADD` instruction with
    /// `lhs` in rA and `rhs` as loaded from memory.  On zero, the sign of
    /// `lhs` is retained.
    ///
    /// Returns the output and overflow flag in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(123).unwrap();
    /// let rhs = Word::try_from(456).unwrap();
    ///
    /// assert_eq!(
    ///     Word::add(lhs, rhs),
    ///     (Word::try_from(123 + 456).unwrap(), false)
    /// );
    /// ```
    ///
    /// On zero:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(-123).unwrap();
    /// let rhs = -lhs;
    ///
    /// assert_eq!(Word::add(lhs, rhs), (Word::NEG_ZERO, false));
    /// ```
    ///
    ///
    /// On overflow/underflow:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(2).unwrap();
    /// let rhs = Word::MAX;
    ///
    /// assert_eq!(Word::add(lhs, rhs), (Word::try_from(1).unwrap(), true));
    /// ```
    pub const fn add(lhs: Word, rhs: Word) -> (Word, bool) {
        // Result can not overflow i32.
        let value = lhs.to_i32() + rhs.to_i32();

        if value == 0 {
            // Retain sign of lhs on zero.
            (Word(lhs.mask_sign()), false)
        } else if value > Word::MAX.to_i32() {
            (Word(value as u32 & Word::VALUE_MASK), true)
        } else if value < Word::MIN.to_i32() {
            (Word(-value as u32 & Word::VALUE_MASK), true)
        } else {
            (unsafe { Word::from_i32_unchecked(value) }, false)
        }
    }

    /// MIX subtraction.
    ///
    /// This behaves in the manner of the MIX `SUB` instruction with
    /// `lhs` in rA and `rhs` as loaded from memory.  On zero, the sign of
    /// `lhs` is retained.
    ///
    /// Returns the output and overflow flag in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(123).unwrap();
    /// let rhs = Word::try_from(456).unwrap();
    ///
    /// assert_eq!(
    ///     Word::sub(lhs,rhs),
    ///     (Word::try_from(123 - 456).unwrap(), false)
    /// );
    /// ```
    ///
    /// On zero:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(123).unwrap();
    /// let rhs = lhs;
    ///
    /// assert_eq!(Word::sub(lhs,rhs), (Word::POS_ZERO, false));
    /// ```
    ///
    ///
    /// On overflow/underflow:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(-2).unwrap();
    /// let rhs = Word::MAX;
    ///
    /// assert_eq!(Word::sub(lhs, rhs), (Word::try_from(1).unwrap(), true));
    /// ```
    pub const fn sub(lhs: Word, rhs: Word) -> (Word, bool) {
        Word::add(lhs, Word(rhs.0 ^ Word::SIGN_MASK))
    }

    /// MIX multiplication.
    ///
    /// This behaves in the manner of the MIX `MUL` instruction with `lhs` in
    /// rA and `rhs` as loaded from memory. The signs of the output words
    /// are both equal to the algebraic product of the signs of `lhs` and
    /// `rhs`,
    ///
    /// Returns the high and low words (rA and rX) of the result in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let lhs = Word::try_from(-123456789).unwrap();
    /// let rhs = Word::try_from(-987654321).unwrap();
    /// let hi = Word::try_from(113558611).unwrap();
    /// let lo = Word::try_from(1006588805).unwrap();
    ///
    /// assert_eq!(Word::mul(lhs, rhs), (hi, lo));
    /// ```
    pub const fn mul(lhs: Word, rhs: Word) -> (Word, Word) {
        let signbit = lhs.mask_sign() ^ rhs.mask_sign();
        let res = lhs.mask_value() as u64 * rhs.mask_value() as u64;
        let hi = (res >> 30) as u32 | signbit;
        let lo = (res as u32 & Word::VALUE_MASK) | signbit;

        (Word(hi), Word(lo))
    }

    /// MIX division.
    ///
    /// This behaves in the manner of the MIX `DIV` instruction with `num_hi`
    /// in rA, `num_lo` in rX, and `denom` loaded from memory. If an overflow
    /// occurs the quotient and remainder are guaranteed to be positive zero,
    /// but in general the MIX specification allows these to be undefined.
    ///
    /// Returns the quotient, remainder, and overflow flag in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let num_hi = Word::POS_ZERO;
    /// let num_lo = Word::try_from(17).unwrap();
    /// let denom = Word::try_from(5).unwrap();
    /// let quot = Word::try_from(3).unwrap();
    /// let rem = Word::try_from(2).unwrap();
    ///
    /// assert_eq!(Word::div(num_hi, num_lo, denom), (quot, rem, false));
    /// ```
    ///
    /// Quotient overflow:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// // Overflow since num_hi >= denom.
    /// let num_hi = Word::try_from(100).unwrap();
    /// let num_lo = Word::POS_ZERO;
    /// let denom = Word::try_from(10).unwrap();
    ///
    /// assert_eq!(
    ///     Word::div(num_hi, num_lo, denom),
    ///     (Word::POS_ZERO, Word::POS_ZERO, true)
    /// );
    /// ```
    ///
    /// Divide by zero:
    ///
    /// ```
    /// use mixlib::num::Word;
    ///
    /// let num_hi = Word::POS_ZERO;
    /// let num_lo = Word::try_from(123).unwrap();
    /// let denom = Word::POS_ZERO;
    ///
    /// assert_eq!(
    ///     Word::div(num_hi, num_lo, denom),
    ///     (Word::POS_ZERO, Word::POS_ZERO, true)
    /// );
    /// ```
    pub const fn div(
        num_hi: Word,
        num_lo: Word,
        denom: Word,
    ) -> (Word, Word, bool) {
        // All overflow conditions.
        if denom.is_zero() || num_hi.mask_value() >= denom.mask_value() {
            return (Word::POS_ZERO, Word::POS_ZERO, true);
        }

        let num_abs = Word::dword_to_u64(num_hi, num_lo);
        let denom_abs = denom.mask_value() as u64;

        let quot_abs = (num_abs / denom_abs) as u32;
        let quot_signbit = num_hi.mask_sign() ^ denom.mask_sign();
        let quot = Word(quot_abs | quot_signbit);

        let rem_abs = (num_abs % denom_abs) as u32;
        let rem_signbit = num_hi.mask_sign();
        let rem = Word(rem_abs | rem_signbit);

        (quot, rem, false)
    }

    /// MIX shift left.
    ///
    /// This behaves in the manner of the MIX `SLAX` operation with `hi` as
    /// rA, `lo` as rX, and `bytes` as the number of bytes to shift.
    ///
    /// The high (rA) and low (rX) words of the output are returned in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let hi = make_word(Sign::Plus, [1, 2, 3, 4, 5]);
    /// let lo = make_word(Sign::Minus, [6, 7, 8, 9, 10]);
    /// let bytes = 3;
    /// let shifted_hi = make_word(Sign::Plus, [4, 5, 6, 7, 8]);
    /// let shifted_lo = make_word(Sign::Minus, [9, 10, 0, 0, 0]);
    ///
    /// assert_eq!(Word::shift_left(hi, lo, bytes), (shifted_hi, shifted_lo));
    /// ```
    pub const fn shift_left(hi: Word, lo: Word, bytes: usize) -> (Word, Word) {
        Word::dword_from_u64(
            hi.mask_sign(),
            lo.mask_sign(),
            Word::dword_to_u64(hi, lo).wrapping_shl((bytes * 6) as u32),
        )
    }

    /// MIX shift right.
    ///
    /// This behaves in the manner of the MIX `SRAX` operation with `hi` as
    /// rA, `lo` as rX, and `bytes` as the number of bytes to shift.
    ///
    /// The high (rA) and low (rX) words of the output are returned in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let hi = make_word(Sign::Plus, [1, 2, 3, 4, 5]);
    /// let lo = make_word(Sign::Minus, [6, 7, 8, 9, 10]);
    /// let bytes = 3;
    /// let shifted_hi = make_word(Sign::Plus, [0, 0, 0, 1, 2]);
    /// let shifted_lo = make_word(Sign::Minus, [3, 4, 5, 6, 7]);
    ///
    /// assert_eq!(Word::shift_right(hi, lo, bytes), (shifted_hi, shifted_lo));
    /// ```
    pub const fn shift_right(
        hi: Word,
        lo: Word,
        bytes: usize,
    ) -> (Word, Word) {
        Word::dword_from_u64(
            hi.mask_sign(),
            lo.mask_sign(),
            Word::dword_to_u64(hi, lo).wrapping_shr((bytes * 6) as u32),
        )
    }

    /// MIX rotate left.
    ///
    /// This behaves in the manner of the MIX `SLC` operation with `hi` as rA,
    /// `lo` as rX, and `bytes` as the number of bytes to shift circularly.
    ///
    /// The high (rA) and low (rX) words of the output are returned in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let hi = make_word(Sign::Plus, [1, 2, 3, 4, 5]);
    /// let lo = make_word(Sign::Minus, [6, 7, 8, 9, 10]);
    /// let bytes = 3;
    /// let rotated_hi = make_word(Sign::Plus, [4, 5, 6, 7, 8]);
    /// let rotated_lo = make_word(Sign::Minus, [9, 10, 1, 2, 3]);
    ///
    /// assert_eq!(Word::rotate_left(hi, lo, bytes), (rotated_hi, rotated_lo));
    /// ```
    pub const fn rotate_left(
        hi: Word,
        lo: Word,
        bytes: usize,
    ) -> (Word, Word) {
        let lbits = 6 * (bytes % 5);
        let rbits = 60 - lbits;
        let uval = Word::dword_to_u64(hi, lo);

        Word::dword_from_u64(
            hi.mask_sign(),
            lo.mask_sign(),
            uval << lbits | uval >> rbits,
        )
    }

    /// MIX rotate right.
    ///
    /// This behaves in the manner of the MIX `SRC` operation with `hi` as rA,
    /// `lo` as rX, and `bytes` as the number of bytes to shift circularly.
    ///
    /// The high (rA) and low (rX) words of the output are returned in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let hi = make_word(Sign::Plus, [1, 2, 3, 4, 5]);
    /// let lo = make_word(Sign::Minus, [6, 7, 8, 9, 10]);
    /// let bytes = 3;
    /// let rotated_hi = make_word(Sign::Plus, [8, 9, 10, 1, 2]);
    /// let rotated_lo = make_word(Sign::Minus, [3, 4, 5, 6, 7]);
    ///
    /// assert_eq!(Word::rotate_right(hi, lo, bytes), (rotated_hi, rotated_lo));
    /// ```
    pub const fn rotate_right(
        hi: Word,
        lo: Word,
        bytes: usize,
    ) -> (Word, Word) {
        let rbits = 6 * (bytes % 5);
        let lbits = 60 - rbits;
        let uval = Word::dword_to_u64(hi, lo);

        Word::dword_from_u64(
            hi.mask_sign(),
            lo.mask_sign(),
            uval << lbits | uval >> rbits,
        )
    }

    /// MIX convert to numeric.
    ///
    /// This behaves in the manner of the MIX `NUM` operation with `hi` as rA
    /// and `lo` as rX.
    ///
    /// Returns the result and overflow flag in order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let hi = make_word(Sign::Minus, [0, 0, 31, 32, 39]);
    /// let lo = make_word(Sign::Plus, [37, 57, 47, 30, 30]);
    /// let value = Word::try_from(-12977700).unwrap();
    ///
    /// assert_eq!(Word::num(hi, lo), (value, false));
    /// ```
    ///
    /// On overflow:
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let hi = Word::from_sign_and_bytes(
    ///     Sign::Plus,
    ///     [39, 0, 0, 0, 0].map(|v| Byte::try_from(v).unwrap())
    /// );
    /// let lo = Word::POS_ZERO;
    /// let value = Word::try_from(410065408).unwrap();
    ///
    /// assert_eq!(Word::num(hi, lo), (value, true));
    /// ```
    pub const fn num(hi: Word, lo: Word) -> (Word, bool) {
        const BYTE_MASK: u64 = Byte::VALUE_MASK as u64;

        let h = hi.0 as u64;
        let l = lo.0 as u64;

        let value = 1000000000 * (((h >> 24) & BYTE_MASK) % 10)
            + 100000000 * (((h >> 18) & BYTE_MASK) % 10)
            + 10000000 * (((h >> 12) & BYTE_MASK) % 10)
            + 1000000 * (((h >> 6) & BYTE_MASK) % 10)
            + 100000 * ((h & BYTE_MASK) % 10)
            + 10000 * (((l >> 24) & BYTE_MASK) % 10)
            + 1000 * (((l >> 18) & BYTE_MASK) % 10)
            + 100 * (((l >> 12) & BYTE_MASK) % 10)
            + 10 * (((l >> 6) & BYTE_MASK) % 10)
            + ((l & BYTE_MASK) % 10);

        let repr = (value as u32 & Word::VALUE_MASK) | hi.mask_sign();
        let overflow = value > Word::VALUE_MASK as u64;

        (Word(repr), overflow)
    }

    /// MIX convert to characters.
    ///
    /// This behaves in the manner of the MIX `CHAR` operation with `hi` as rA
    /// and `lo` as rX. Note this means that `lo` is only used for its sign.
    ///
    /// Returns the high (rA) and low (rX) words of the result in order.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::num::{Sign, Byte, Word};
    ///
    /// let make_word = |sign, bytes: [u8; 5]| {
    ///     Word::from_sign_and_bytes(
    ///         sign,
    ///         bytes.map(|v| Byte::try_from(v).unwrap())
    ///     )
    /// };
    ///
    /// let hi = Word::try_from(-12977699).unwrap();
    /// let lo = Word::POS_ZERO;
    /// let char_hi = make_word(Sign::Minus, [30, 30, 31, 32, 39]);
    /// let char_lo = make_word(Sign::Plus, [37, 37, 36, 39, 39]);
    ///
    /// assert_eq!(Word::char(hi, lo), (char_hi, char_lo));
    /// ```
    pub const fn char(hi: Word, lo: Word) -> (Word, Word) {
        let mut value = hi.mask_value();
        let mut bytes = [Byte::MIN; 10];
        let mut index = 10;

        while index != 0 {
            index -= 1;
            bytes[index] = Byte(30 + (value % 10) as u8);
            value /= 10;
        }

        (
            Word::from_sign_and_bytes(
                hi.sign(),
                [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4]],
            ),
            Word::from_sign_and_bytes(
                lo.sign(),
                [bytes[5], bytes[6], bytes[7], bytes[8], bytes[9]],
            ),
        )
    }

    const SIGN_MASK: u32 = 1 << 30;
    const VALUE_MASK: u32 = (1 << 30) - 1;

    const fn mask_sign(self) -> u32 {
        self.0 & Word::SIGN_MASK
    }

    const fn mask_value(self) -> u32 {
        self.0 & Word::VALUE_MASK
    }

    const fn dword_to_u64(hi: Word, lo: Word) -> u64 {
        ((hi.mask_value() as u64) << 30) | lo.mask_value() as u64
    }

    const fn dword_from_u64(
        hi_signbit: u32,
        lo_signbit: u32,
        value: u64,
    ) -> (Word, Word) {
        let hi_value = ((value >> 30) as u32) & Word::VALUE_MASK;
        let lo_value = (value as u32) & Word::VALUE_MASK;
        let hi_word = Word(hi_value | hi_signbit);
        let lo_word = Word(lo_value | lo_signbit);

        (hi_word, lo_word)
    }
}

impl Neg for Word {
    type Output = Word;

    fn neg(self) -> Self::Output {
        Word(self.0 ^ Word::SIGN_MASK)
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
        f.write_fmt(format_args!("{}{}", self.sign(), self.mask_value()))
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

    /// Converts an `u16` to a [`MemoryAddress`] without checking whether it
    /// is valid.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value >
    /// MemoryAddress::MAX.to_u16()`.
    pub const unsafe fn from_u16_unchecked(value: u16) -> MemoryAddress {
        debug_assert!(value <= MemoryAddress::MAX.0);
        MemoryAddress(value)
    }

    /// Converts `self` to a `u16`.
    pub const fn to_u16(self) -> u16 {
        self.0
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
    pub const MAX: LocationCounter =
        LocationCounter(LocationCounter::VALUE_MASK);

    /// Converts an `u16` to a [`LocationCounter`] without checking whether
    /// it is valid.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value >
    /// LocationCounter::MAX.to_u16()`.
    pub const unsafe fn from_u16_unchecked(value: u16) -> LocationCounter {
        debug_assert!(value <= LocationCounter::MAX.0);
        LocationCounter(value)
    }

    /// Converts `self` to a `u16`.
    pub const fn to_u16(self) -> u16 {
        self.0
    }

    /// Returns the incremented location counter or `None` if overflow occurs.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use mixlib::num::LocationCounter;
    ///
    /// let one = LocationCounter::try_from(1).unwrap();
    /// let two = LocationCounter::try_from(2).unwrap();
    ///
    /// assert_eq!(one.increment(), Some(two));
    /// ```
    ///
    /// On overflow:
    ///
    /// ```
    /// use mixlib::num::LocationCounter;
    ///
    /// assert_eq!(LocationCounter::MAX.increment(), None);
    /// ```
    pub const fn increment(self) -> Option<LocationCounter> {
        if self.0 == Self::MAX.0 { None } else { Some(Self(self.0 + 1)) }
    }

    const VALUE_MASK: u16 = (1 << 12) - 1;
}

macro_rules! impl_int_conversions {
    (
        main_type = $main_type:ty;
        repr_type = $repr_type:ty;
        main_from_repr_unchecked = $main_from_repr_unchecked:ident;
        main_to_repr = $main_to_repr:ident;
        from_T_for_main = $($from_T_for_main:ty),*;
        try_from_T_for_main = $($try_from_T_for_main:ty),*;
        from_main_for_T = $($from_main_for_T:ty),*;
        try_from_main_for_T = $($try_from_main_for_T:ty),*;
    ) => {
        impl From<$main_type> for $repr_type {
            fn from(value: $main_type) -> Self {
                value.$main_to_repr()
            }
        }

        impl TryFrom<$repr_type> for $main_type {
            type Error = TryFromIntError;

            fn try_from(value: $repr_type) -> Result<Self, Self::Error> {
                const MIN: $repr_type = <$main_type>::MIN.$main_to_repr();
                const MAX: $repr_type = <$main_type>::MAX.$main_to_repr();

                if matches!(value, MIN..=MAX) {
                    Ok(unsafe { <$main_type>::$main_from_repr_unchecked(value) })
                } else {
                    Err(TryFromIntError(()))
                }
            }
        }

        $(
            impl From<$from_T_for_main> for $main_type {
                fn from(value: $from_T_for_main) -> Self {
                    let repr = <$repr_type>::from(value);
                    unsafe { <$main_type>::$main_from_repr_unchecked(repr) }
                }
            }
        )*
        $(
            impl TryFrom<$try_from_T_for_main> for $main_type {
                type Error = TryFromIntError;

                fn try_from(value: $try_from_T_for_main) -> Result<Self, Self::Error> {
                    <$repr_type>::try_from(value)
                        .map_err(|_| TryFromIntError(()))
                        .and_then(<$main_type>::try_from)
                }
            }
        )*
        $(
            impl From<$main_type> for $from_main_for_T {
                fn from(value: $main_type) -> Self {
                    let repr = <$repr_type>::from(value);
                    <$from_main_for_T>::from(repr)
                }
            }
        )*
        $(
            impl TryFrom<$main_type> for $try_from_main_for_T {
                type Error = TryFromIntError;

                fn try_from(value: $main_type) -> Result<Self, Self::Error> {
                    let repr = <$repr_type>::from(value);
                    <$try_from_main_for_T>::try_from(repr)
                        .map_err(|_| TryFromIntError(()))
                }
            }
        )*
    };
}

impl_int_conversions! {
    main_type = Byte;
    repr_type = u8;
    main_from_repr_unchecked = from_u8_unchecked;
    main_to_repr = to_u8;
    from_T_for_main = ;
    try_from_T_for_main = u16, u32, u64, u128, usize, i8, i16, i32, i64, i128,
        isize, Short, Word, MemoryAddress, LocationCounter;
    from_main_for_T = u16, u32, u64, u128, usize, i16, i32, i64, i128, isize;
    try_from_main_for_T = ;
}

// Extra impl needed since `i8: !From<u8>`.
impl From<Byte> for i8 {
    fn from(value: Byte) -> Self {
        value.0 as i8
    }
}

impl_int_conversions! {
    main_type = Short;
    repr_type = i16;
    main_from_repr_unchecked = from_i16_unchecked;
    main_to_repr = to_i16;
    from_T_for_main = u8, i8, Byte, MemoryAddress, LocationCounter;
    try_from_T_for_main = u16, u32, u64, u128, usize, i32, i64, i128, isize,
        Word;
    from_main_for_T = i32, i64, i128;
    try_from_main_for_T = u8, u16, u32, u64, u128, usize, i8, isize;
}

impl_int_conversions! {
    main_type = Word;
    repr_type = i32;
    main_from_repr_unchecked = from_i32_unchecked;
    main_to_repr = to_i32;
    from_T_for_main = u8, i8, u16, i16, Byte, Short, MemoryAddress,
        LocationCounter;
    try_from_T_for_main = u32, u64, u128, usize, i64, i128, isize;
    from_main_for_T = i64, i128;
    try_from_main_for_T = u8, u16, u32, u64, u128, usize, i8, i16, isize;
}

impl_int_conversions! {
    main_type = MemoryAddress;
    repr_type = u16;
    main_from_repr_unchecked = from_u16_unchecked;
    main_to_repr = to_u16;
    from_T_for_main = u8, Byte;
    try_from_T_for_main = u32, u64, u128, usize, i8, i16, i32, i64, i128,
        isize, Short, Word, LocationCounter;
    from_main_for_T = u32, u64, u128, i32, i64, i128;
    try_from_main_for_T = u8, usize, i8, isize;
}

// Extra impl needed since `i16: !From<u16>`.
impl From<MemoryAddress> for i16 {
    fn from(value: MemoryAddress) -> Self {
        value.0 as i16
    }
}

impl_int_conversions! {
    main_type = LocationCounter;
    repr_type = u16;
    main_from_repr_unchecked = from_u16_unchecked;
    main_to_repr = to_u16;
    from_T_for_main = u8, Byte, MemoryAddress;
    try_from_T_for_main = u32, u64, u128, usize, i8, i16, i32, i64, i128,
        isize, Short, Word;
    from_main_for_T = u32, u64, u128, i32, i64, i128;
    try_from_main_for_T = u8, usize, i8, isize;
}

// Extra impl needed since `i16: !From<u16>`.
impl From<LocationCounter> for i16 {
    fn from(value: LocationCounter) -> Self {
        value.0 as i16
    }
}
