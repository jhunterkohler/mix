//! MIX characters.

use std::error;
use std::fmt;
use std::fmt::Write;
use std::mem::transmute;

use crate::num::Byte;

macro_rules! define_char {
    ($(
        name = $name:ident,
        value = $value:literal,
        ascii = $ascii:literal,
        unicode = $unicode:literal,
        doc = $doc:literal
    );*;) => {
        /// A MIX character.
        #[repr(u8)]
        #[derive(
            Clone, Copy, PartialEq, Eq, Hash, Debug, Default, PartialOrd, Ord,
        )]
        pub enum Char {
            #[default]
            $(#[doc = $doc] $name = $value,)*
        }

        impl Char {
            /// Lowest value character.
            pub const MIN: Char = Char::Space;

            /// Highest value character.
            pub const MAX: Char = Char::Apostrophe;

            /// The maximum number of bytes required to encode a `Char` in
            /// UTF-8.
            pub const MAX_LEN_UTF8: usize = 2;

            /// Converts the character to the standard unicode `char` type.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::char::Char;
            ///
            /// assert_eq!(Char::CapitalA.to_unicode(), 'A');
            /// assert_eq!(Char::CapitalSigma.to_unicode(), 'Σ');
            /// ```
            pub const fn to_unicode(self) -> char {
                match self {
                    $(Self::$name => $unicode,)*
                }
            }

            /// Converts a mix character to the standard unicode `char` with
            /// project's convenience replacements. This guarentees the output
            /// is also ascii.
            ///
            /// The replacements are `'~'` for [`Char::CapitalDelta`],
            /// `'['` for [`Char::CapitalSigma`], and `'#'` for
            /// [`Char::CapitalPi`].
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::char::Char;
            ///
            /// assert_eq!(
            ///     Char::CapitalA.to_unicode_with_replacement(),
            ///     'A'
            /// );
            ///
            /// assert_eq!(
            ///     Char::CapitalDelta.to_unicode_with_replacement(),
            ///     '~'
            /// );
            ///
            /// assert_eq!(
            ///     Char::CapitalSigma.to_unicode_with_replacement(),
            ///     '['
            /// );
            ///
            /// assert_eq!(
            ///     Char::CapitalPi.to_unicode_with_replacement(),
            ///     '#'
            /// );
            /// ```
            pub const fn to_unicode_with_replacement(self) -> char {
                match self {
                    $(Self::$name => $ascii,)*
                }
            }

            /// Converts a standard unicode `char` to a MIX character,
            /// returning `None` when the character is invalid.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::char::Char;
            ///
            /// assert_eq!(Char::from_unicode('A'), Some(Char::CapitalA));
            /// assert_eq!(Char::from_unicode('Σ'), Some(Char::CapitalSigma));
            /// assert_eq!(Char::from_unicode('\n'), None);
            /// ```
            pub const fn from_unicode(value: char) -> Option<Char> {
                match value {
                    $($unicode => Some(Self::$name),)*
                    _ => None
                }
            }

            /// Converts a standard unicode `char` to a MIX character using the
            /// project's convenience replacements, returning `None` when a
            /// character is invalid.
            ///
            /// The replacements are `'~'` for [`Char::CapitalDelta`],
            /// `'['` for [`Char::CapitalSigma`], and `'#'` for
            /// [`Char::CapitalPi`]. Note that the exact unicode characters are
            /// still accepted.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// use mixlib::char::Char;
            ///
            /// assert_eq!(
            ///     Char::from_unicode_with_replacement('A'),
            ///     Some(Char::CapitalA)
            /// );
            ///
            /// assert_eq!(
            ///     Char::from_unicode_with_replacement('Σ'),
            ///     Some(Char::CapitalSigma)
            /// );
            ///
            /// assert_eq!(
            ///     Char::from_unicode_with_replacement('\n'),
            ///     None
            /// );
            /// ```
            ///
            /// Usage with replacements:
            ///
            /// ```
            /// use mixlib::char::Char;
            ///
            /// assert_eq!(
            ///     Char::from_unicode_with_replacement('~'),
            ///     Some(Char::CapitalDelta)
            /// );
            ///
            /// assert_eq!(
            ///     Char::from_unicode_with_replacement('['),
            ///     Some(Char::CapitalSigma)
            /// );
            ///
            /// assert_eq!(
            ///     Char::from_unicode_with_replacement('#'),
            ///     Some(Char::CapitalPi)
            /// );
            /// ```
            pub const fn from_unicode_with_replacement(
                value: char
            ) -> Option<Char> {
                match value {
                    $($unicode => Some(Self::$name),)*
                    '~' => Some(Self::CapitalDelta),
                    '[' => Some(Self::CapitalSigma),
                    '#' => Some(Self::CapitalPi),
                    _ => None
                }
            }

            /// Converts a digit (0 through 9) into the corresponding character
            /// ([`Char::Digit0`] through [`Char::Digit9`]), or returns `None`
            /// otherwise.
            ///
            /// # Examples
            ///
            /// ```
            /// use mixlib::char::Char;
            ///
            /// assert_eq!(Char::from_digit(5), Some(Char::Digit5));
            /// assert_eq!(Char::from_digit(11), None);
            /// ```
            pub const fn from_digit(num: u32) -> Option<Char> {
                if num < 10 {
                    Some(unsafe { transmute(Char::Digit0 as u8 + num as u8) })
                } else {
                    None
                }
            }

            /// Encodes this character as UTF-8 into the provided byte buffer,
            /// and then returns the subslice of the buffer that contains the
            /// encoded character.
            ///
            /// # Panics
            ///
            /// Panics if the buffer is not large enough a buffer of length
            /// `Char::MAX_LEN_UTF8` is large enough to encode any `Char`.
            ///
            /// # Examples
            pub const fn encode_utf8(self, dest: &mut [u8]) -> &str {
                self.to_unicode().encode_utf8(dest)
            }
        }
    }
}

define_char! {
    name = Space,           value = 0,  ascii = ' ',  unicode = ' ',        doc = "U+0020";
    name = CapitalA,        value = 1,  ascii = 'A',  unicode = 'A',        doc = "U+0041";
    name = CapitalB,        value = 2,  ascii = 'B',  unicode = 'B',        doc = "U+0042";
    name = CapitalC,        value = 3,  ascii = 'C',  unicode = 'C',        doc = "U+0043";
    name = CapitalD,        value = 4,  ascii = 'D',  unicode = 'D',        doc = "U+0044";
    name = CapitalE,        value = 5,  ascii = 'E',  unicode = 'E',        doc = "U+0045";
    name = CapitalF,        value = 6,  ascii = 'F',  unicode = 'F',        doc = "U+0046";
    name = CapitalG,        value = 7,  ascii = 'G',  unicode = 'G',        doc = "U+0047";
    name = CapitalH,        value = 8,  ascii = 'H',  unicode = 'H',        doc = "U+0048";
    name = CapitalI,        value = 9,  ascii = 'I',  unicode = 'I',        doc = "U+0049";
    name = CapitalDelta,    value = 10, ascii = '~',  unicode = '\u{0394}', doc = "U+0394";
    name = CapitalJ,        value = 11, ascii = 'J',  unicode = 'J',        doc = "U+004A";
    name = CapitalK,        value = 12, ascii = 'K',  unicode = 'K',        doc = "U+004B";
    name = CapitalL,        value = 13, ascii = 'L',  unicode = 'L',        doc = "U+004C";
    name = CapitalM,        value = 14, ascii = 'M',  unicode = 'M',        doc = "U+004D";
    name = CapitalN,        value = 15, ascii = 'N',  unicode = 'N',        doc = "U+004E";
    name = CapitalO,        value = 16, ascii = 'O',  unicode = 'O',        doc = "U+004F";
    name = CapitalP,        value = 17, ascii = 'P',  unicode = 'P',        doc = "U+0050";
    name = CapitalQ,        value = 18, ascii = 'Q',  unicode = 'Q',        doc = "U+0051";
    name = CapitalR,        value = 19, ascii = 'R',  unicode = 'R',        doc = "U+0052";
    name = CapitalSigma,    value = 20, ascii = '[',  unicode = '\u{03A3}', doc = "U+04A3";
    name = CapitalPi,       value = 21, ascii = '#',  unicode = '\u{03A0}', doc = "U+03A0";
    name = CapitalS,        value = 22, ascii = 'S',  unicode = 'S',        doc = "U+0053";
    name = CapitalT,        value = 23, ascii = 'T',  unicode = 'T',        doc = "U+0054";
    name = CapitalU,        value = 24, ascii = 'U',  unicode = 'U',        doc = "U+0055";
    name = CapitalV,        value = 25, ascii = 'V',  unicode = 'V',        doc = "U+0056";
    name = CapitalW,        value = 26, ascii = 'W',  unicode = 'W',        doc = "U+0057";
    name = CapitalX,        value = 27, ascii = 'X',  unicode = 'X',        doc = "U+0058";
    name = CapitalY,        value = 28, ascii = 'Y',  unicode = 'Y',        doc = "U+0059";
    name = CapitalZ,        value = 29, ascii = 'Z',  unicode = 'Z',        doc = "U+0060";
    name = Digit0,          value = 30, ascii = '0',  unicode = '0',        doc = "U+0030";
    name = Digit1,          value = 31, ascii = '1',  unicode = '1',        doc = "U+0031";
    name = Digit2,          value = 32, ascii = '2',  unicode = '2',        doc = "U+0032";
    name = Digit3,          value = 33, ascii = '3',  unicode = '3',        doc = "U+0033";
    name = Digit4,          value = 34, ascii = '4',  unicode = '4',        doc = "U+0034";
    name = Digit5,          value = 35, ascii = '5',  unicode = '5',        doc = "U+0035";
    name = Digit6,          value = 36, ascii = '6',  unicode = '6',        doc = "U+0036";
    name = Digit7,          value = 37, ascii = '7',  unicode = '7',        doc = "U+0037";
    name = Digit8,          value = 38, ascii = '8',  unicode = '8',        doc = "U+0038";
    name = Digit9,          value = 39, ascii = '9',  unicode = '9',        doc = "U+0039";
    name = FullStop,        value = 40, ascii = '.',  unicode = '.',        doc = "U+002E";
    name = Comma,           value = 41, ascii = ',',  unicode = ',',        doc = "U+002C";
    name = LeftParenthesis, value = 42, ascii = '(',  unicode = '(',        doc = "U+0028";
    name = RightParenthesis,value = 43, ascii = ')',  unicode = ')',        doc = "U+0029";
    name = PlusSign,        value = 44, ascii = '+',  unicode = '+',        doc = "U+002B";
    name = HyphenMinus,     value = 45, ascii = '-',  unicode = '-',        doc = "U+002D";
    name = Asterisk,        value = 46, ascii = '*',  unicode = '*',        doc = "U+002A";
    name = Solidus,         value = 47, ascii = '/',  unicode = '/',        doc = "U+002F";
    name = EqualsSign,      value = 48, ascii = '=',  unicode = '=',        doc = "U+003D";
    name = DollarSign,      value = 49, ascii = '$',  unicode = '$',        doc = "U+0024";
    name = LessThanSign,    value = 50, ascii = '<',  unicode = '<',        doc = "U+003C";
    name = GreaterThanSign, value = 51, ascii = '>',  unicode = '>',        doc = "U+003E";
    name = CommercialAt,    value = 52, ascii = '@',  unicode = '@',        doc = "U+0040";
    name = Semicolon,       value = 53, ascii = ';',  unicode = ';',        doc = "U+003B";
    name = Colon,           value = 54, ascii = ':',  unicode = ':',        doc = "U+003A";
    name = Apostrophe,      value = 55, ascii = '\'', unicode = '\'',       doc = "U+0027";
}

impl From<Char> for char {
    fn from(value: Char) -> Self {
        value.to_unicode()
    }
}

impl From<Char> for Byte {
    fn from(value: Char) -> Self {
        unsafe { transmute(value) }
    }
}

impl From<Char> for u8 {
    fn from(value: Char) -> Self {
        value as u8
    }
}

/// An error that can be returned when converting to between character types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryFromCharError(());

impl error::Error for TryFromCharError {}

impl fmt::Display for TryFromCharError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("converted value is an invalid character")
    }
}

impl TryFrom<char> for Char {
    type Error = TryFromCharError;

    /// Converts from `char` using `Char::from_unicode`,
    fn try_from(value: char) -> Result<Self, Self::Error> {
        Self::from_unicode(value).ok_or(TryFromCharError(()))
    }
}

impl TryFrom<Byte> for Char {
    type Error = TryFromCharError;

    fn try_from(value: Byte) -> Result<Self, Self::Error> {
        Char::try_from(u8::from(value))
    }
}

impl TryFrom<u8> for Char {
    type Error = TryFromCharError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value <= Self::MAX as u8 {
            Ok(unsafe { transmute(value) })
        } else {
            Err(TryFromCharError(()))
        }
    }
}

impl fmt::Display for Char {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_char(self.to_unicode())
    }
}
