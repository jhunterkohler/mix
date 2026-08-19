//! # mixlib
//!
//! This crate provides utilities for working with Donald Knuth's MIX
//! computer architecture and MIXAL (the MIX assembly language).
#![allow(
    clippy::missing_transmute_annotations,
    clippy::len_without_is_empty,
    clippy::manual_range_contains
)]
#![doc(test(attr(deny(unused_imports, dead_code))))]

pub mod asm;
pub mod ast;
pub mod bin;
pub mod char;
pub mod dev;
pub mod emu;
pub mod fmt;
pub mod mem;
pub mod num;
pub mod source;
pub mod symbol;

#[doc(hidden)]
pub mod __private {
    pub use mixlib_macros::{__byte, __short, __word};
}

/// Create a [`Byte`] constant expression.
///
/// Takes a literal number and creates a [`Byte`], giving a compilation error
/// if the value is invalid.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::{byte, num::Byte};
///
/// // Can be used as a constant expression.
/// const BYTE_10: Byte = byte!(10);
///
/// assert_eq!(BYTE_10, Byte::try_from(10).unwrap());
/// ```
///
/// Non-example:
///
/// ```compile_error
/// use mixlib::{byte, num::Byte};
///
/// // error: literal value '10000' out of range of MIX byte (0..=63)
/// const BYTE: Byte = byte!(10000);
/// ```
///
/// [`Byte`]: num::Byte
#[macro_export]
macro_rules! byte {
    ($($tt:tt)*) => {
        $crate::__private::__byte!($crate, $($tt)*)
    };
}

/// Create a [`Short`] constant expression.
///
/// Takes a literal number, or a sign and series of bytes, and creates a
/// [`Short`], giving a compilation error if the value is invalid. The macro
/// interprets `-0` as `Short::NEG_ZERO`.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::{short, num::{Short, Byte}};
///
/// // Can be used as a literal expression.
/// const SHORT_10: Short = short!(10);
/// const SHORT_12: Short = short![+, 1, 2];
///
/// assert_eq!(SHORT_10, Short::try_from(10).unwrap());
/// assert_eq!(SHORT_12.bytes(), [1, 2].map(|b| Byte::try_from(b).unwrap()));
/// ```
///
/// Negative zero:
///
/// ```
/// use mixlib::{short, num::Sign};
///
/// assert_eq!(short!(-0).sign(), Sign::Minus);
/// ```
///
/// Non-example:
///
/// ```compile_error
/// use mixlib::{Short, num::Short};
///
/// // error: literal value '10000' out of range of MIX Short (-4095..=4095)
/// const Short: Short = Short!(10000);
/// ```
///
/// [`Short`]: num::Short
#[macro_export]
macro_rules! short {
    ($($tt:tt)*) => {
        $crate::__private::__short!($crate, $($tt)*)
    };
}

/// Create a [`Word`] constant expression.
///
/// Takes a literal number, or a sign and series of bytes, and creates a
/// [`Word`], giving a compilation error if the value is invalid. The macro
/// interprets `-0` as `Word::NEG_ZERO`.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use mixlib::{word, num::{Word, Byte}};
///
/// // Can be used as a literal expression.
/// const WORD_10: Word = word!(10);
/// const WORD_12345: Word = word![+, 1, 2, 3, 4, 5];
///
/// assert_eq!(WORD_10, Word::try_from(10).unwrap());
/// assert_eq!(WORD_12345.bytes(), [1, 2, 3, 4, 5].map(|b| Byte::try_from(b).unwrap()));
/// ```
///
/// Negative zero:
///
/// ```
/// use mixlib::{word, num::Sign};
///
/// assert_eq!(word!(-0).sign(), Sign::Minus);
/// ```
///
/// Non-example:
///
/// ```compile_error
/// use mixlib::{word, num::Word};
///
/// // error: literal value '10000000000' out of range of MIX word (-1073741823..=1073741823)
/// const WORD: Word = word!(10000000000);
/// ```
///
/// [`Word`]: num::Word
#[macro_export]
macro_rules! word {
    ($($tt:tt)*) => {
        $crate::__private::__word!($crate, $($tt)*)
    };
}

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_error!("'target_pointer_width' must be '32' or '64'");
