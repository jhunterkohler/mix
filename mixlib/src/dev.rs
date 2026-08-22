//! MIX's input-output device system.
//!
//! MIX addresses each peripheral device by a unit number 0 through 20,
//! grouped into the following classes (see Knuth, *TAOCP* Vol. 1, §1.3.1):
//!
//! | Unit | Device                                 | Block size |
//! |------|-----------------------------------------|------------|
//! | 0-7  | Tape unit `t` (`0 <= t <= 7`)             | 100 words  |
//! | 8-15 | Disk or drum unit `d` (`8 <= d <= 15`)    | 100 words  |
//! | 16   | Card reader                              | 16 words   |
//! | 17   | Card punch                               | 16 words   |
//! | 18   | Line printer                             | 24 words   |
//! | 19   | Typewriter terminal                      | 14 words   |
//! | 20   | Paper tape                               | 14 words   |
//!
//! Tape and disk/drum units transfer whole [`Word`]s in a binary format;
//! every other unit transfers MIX characters, five per word, one line
//! (terminated by `\n`, or by `\r` on the terminal) per block. On character
//! input, bytes past the end of a short line are filled with blanks and the
//! sign of every word is set to plus; on character output, word signs are
//! ignored.
//!
//! The device adapters included function synchronously and thus are always
//! ready unlike real MIX hardware.

use std::error;
use std::fmt;
use std::io;
use std::mem;
use std::mem::transmute;

use crate::bin::Decode;
use crate::bin::Encode;
use crate::char::Char;
use crate::num::Sign;
use crate::num::{Byte, Short, Word};

/// Number of bytes used to encode one [`Word`] in the binary format used by
/// [`Tape`] and [`Disk`]. Block byte offsets are this many times a device's
/// [`DeviceKind::block_size`].
const WORD_ENCODED_LEN: usize = 4;

/// Whether a [`DeviceKind`] transfers binary words or MIX characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DeviceMode {
    /// Whole [`Word`]s in `mixlib`'s binary encoding.
    Word,
    /// MIX characters, five per word, as a line of text.
    Char,
}

/// The class of peripheral device identified by a [`DeviceUnit`].
///
/// Every unit within a class shares the same block size and transfer mode;
/// see [`DeviceKind::block_size`] and [`DeviceKind::mode`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DeviceKind {
    Tape,
    Disk,
    CardReader,
    CardPunch,
    LinePrinter,
    Terminal,
    PaperTape,
}

impl DeviceKind {
    /// Returns the fixed number of words transferred by a single `IN` or
    /// `OUT` instruction on this class of device (see the table in the
    /// [module documentation](self)).
    pub const fn block_size(self) -> usize {
        use DeviceKind::*;
        match self {
            Tape | Disk => 100,
            CardReader | CardPunch => 16,
            LinePrinter => 24,
            Terminal | PaperTape => 14,
        }
    }

    /// Returns whether this device transfers data as binary [`Word`]s
    /// ([`DeviceMode::Word`], tape and disk/drum) or as MIX characters
    /// ([`DeviceMode::Char`], every other unit).
    pub const fn mode(self) -> DeviceMode {
        use DeviceKind::*;
        match self {
            Tape | Disk => DeviceMode::Word,
            _ => DeviceMode::Char,
        }
    }

    pub const fn supports_input(self) -> bool {
        use DeviceKind::*;
        match self {
            CardPunch | LinePrinter => false,
            _ => true,
        }
    }

    pub const fn supports_output(self) -> bool {
        use DeviceKind::*;
        match self {
            CardReader => false,
            _ => true,
        }
    }
}

/// Error returned by [`DeviceUnit::try_from`] when a value is not a valid
/// unit number (i.e., greater than [`DeviceUnit::MAX`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct InvalidDeviceUnitError(());

impl fmt::Display for InvalidDeviceUnitError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid device unit")
    }
}

impl error::Error for InvalidDeviceUnitError {}

/// A MIX device unit number, from 0 ([`Tape0`](DeviceUnit::Tape0)) through
/// 20 ([`PaperTape`](DeviceUnit::PaperTape)).
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeviceUnit {
    Tape0 = 0,
    Tape1 = 1,
    Tape2 = 2,
    Tape3 = 3,
    Tape4 = 4,
    Tape5 = 5,
    Tape6 = 6,
    Tape7 = 7,
    Disk0 = 8,
    Disk1 = 9,
    Disk2 = 10,
    Disk3 = 11,
    Disk4 = 12,
    Disk5 = 13,
    Disk6 = 14,
    Disk7 = 15,
    CardReader = 16,
    CardPunch = 17,
    LinePrinter = 18,
    Terminal = 19,
    PaperTape = 20,
}

impl DeviceUnit {
    /// Lowest valid unit number ([`Tape0`](DeviceUnit::Tape0), unit 0).
    pub const MIN: DeviceUnit = DeviceUnit::Tape0;

    /// Highest valid unit number ([`PaperTape`](DeviceUnit::PaperTape), unit
    /// 20).
    pub const MAX: DeviceUnit = DeviceUnit::PaperTape;

    pub const fn to_usize(self) -> usize {
        self as usize
    }

    /// Converts a unit number to a [`DeviceUnit`], or `None` if `value` is
    /// greater than [`DeviceUnit::MAX`].
    pub const fn from_usize(value: usize) -> Option<DeviceUnit> {
        if value <= DeviceUnit::MAX as usize {
            // SAFETY: Just ensured `value` is a valid device unit.
            Some(unsafe { DeviceUnit::from_usize_unchecked(value) })
        } else {
            None
        }
    }

    /// Converts a unit number to a [`DeviceUnit`] without checking validity.
    ///
    /// # Safety
    ///
    /// `value` must be at most [`DeviceUnit::MAX`] as a `usize`.
    pub const unsafe fn from_usize_unchecked(value: usize) -> DeviceUnit {
        debug_assert!(value <= DeviceUnit::MAX as usize);

        // SAFETY: `value` being valid is precondition.
        unsafe { transmute(value as u8) }
    }

    pub const fn to_byte(self) -> Byte {
        unsafe { Byte::from_u8_unchecked(self as u8) }
    }

    pub const fn from_byte(value: Byte) -> Option<Self> {
        Self::from_usize(value.to_u8() as usize)
    }

    /// Returns the class of peripheral device that this unit belongs to.
    pub const fn kind(self) -> DeviceKind {
        use DeviceUnit::*;
        match self {
            Tape0 | Tape1 | Tape2 | Tape3 | Tape4 | Tape5 | Tape6 | Tape7 => {
                DeviceKind::Tape
            }
            Disk0 | Disk1 | Disk2 | Disk3 | Disk4 | Disk5 | Disk6 | Disk7 => {
                DeviceKind::Disk
            }
            CardReader => DeviceKind::CardReader,
            CardPunch => DeviceKind::CardPunch,
            LinePrinter => DeviceKind::LinePrinter,
            Terminal => DeviceKind::Terminal,
            PaperTape => DeviceKind::PaperTape,
        }
    }

    pub fn iter() -> impl Iterator<Item = Self> {
        (Self::MIN as u8..=Self::MAX as u8)
            .into_iter()
            .map(|x| unsafe { mem::transmute(x) })
    }
}

impl From<DeviceUnit> for usize {
    fn from(value: DeviceUnit) -> Self {
        value as usize
    }
}

impl From<DeviceUnit> for Byte {
    fn from(value: DeviceUnit) -> Self {
        Byte::from_u8(value as u8).unwrap()
    }
}

impl TryFrom<usize> for DeviceUnit {
    type Error = InvalidDeviceUnitError;

    fn try_from(value: usize) -> std::result::Result<Self, Self::Error> {
        DeviceUnit::from_usize(value).ok_or(InvalidDeviceUnitError(()))
    }
}

impl TryFrom<Byte> for DeviceUnit {
    type Error = InvalidDeviceUnitError;

    fn try_from(value: Byte) -> std::result::Result<Self, Self::Error> {
        DeviceUnit::try_from(usize::from(value))
    }
}

pub unsafe trait Device {
    fn kind(&self) -> DeviceKind;

    unsafe fn buf(&self) -> &[Word];

    unsafe fn buf_mut(&self) -> &mut [Word];

    unsafe fn input(&mut self, block: Word);

    unsafe fn output(&mut self, block: Word);

    unsafe fn control(&mut self, arg: Short, block: Word);

    fn wait(&mut self);

    fn is_ready(&self) -> bool;
}

impl fmt::Debug for dyn Device {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("dyn Device")
    }
}

const DEVICES_LEN: usize = DeviceUnit::MAX as usize + 1;

#[derive(Debug, Default)]
pub struct DeviceList {
    devices: [Option<Box<dyn Device>>; DEVICES_LEN],
}

impl DeviceList {
    pub fn get(&self, unit: DeviceUnit) -> Option<&dyn Device> {
        self.devices[usize::from(unit)].as_deref()
    }

    pub fn get_mut(&mut self, unit: DeviceUnit) -> Option<&mut dyn Device> {
        match &mut self.devices[usize::from(unit)] {
            Some(dev) => Some(dev.as_mut()),
            None => None,
        }
    }

    pub fn take(&mut self, unit: DeviceUnit) -> Option<Box<dyn Device>> {
        self.devices[usize::from(unit)].take()
    }

    pub fn replace(
        &mut self,
        unit: DeviceUnit,
        dev: Box<dyn Device>,
    ) -> Result<Option<Box<dyn Device>>, Box<dyn Device>> {
        if dev.kind() == unit.kind() {
            Ok(self.devices[usize::from(unit)].replace(dev))
        } else {
            Err(dev)
        }
    }
}

pub trait WordWrite {
    fn write_words(&mut self, buf: &[Word]) -> io::Result<()>;
}

impl<W: io::Write> WordWrite for W {
    fn write_words(&mut self, buf: &[Word]) -> io::Result<()> {
        for word in buf {
            word.encode(&mut *self)?;
        }

        Ok(())
    }
}

pub trait WordRead {
    fn read_words(&mut self, buf: &mut [Word]) -> io::Result<()>;
}

impl<R: io::Read> WordRead for R {
    fn read_words(&mut self, buf: &mut [Word]) -> io::Result<()> {
        for word in buf {
            *word = Decode::decode(&mut *self)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidOutputCharError {
    pub word_pos: usize,
    pub byte_pos: usize,
    pub word: Word,
    pub byte: Byte,
}

impl fmt::Display for InvalidOutputCharError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl error::Error for InvalidOutputCharError {}

impl From<InvalidOutputCharError> for io::Error {
    fn from(value: InvalidOutputCharError) -> Self {
        io::Error::other(value)
    }
}

pub trait CharWrite {
    fn write_chars(&mut self, buf: &[Word]) -> io::Result<()>;
}

impl<W: io::Write> CharWrite for W {
    fn write_chars(&mut self, buf: &[Word]) -> io::Result<()> {
        for (word_pos, word) in buf.iter().copied().enumerate() {
            let (_, bytes) = word.to_sign_bytes();
            let mut utf8 = [0; 5 * Char::MAX_LEN_UTF8];
            let mut utf8_offset = 0;

            for (byte_pos, byte) in bytes.iter().copied().enumerate() {
                let c = Char::try_from(byte).map_err(|_| {
                    InvalidOutputCharError { word_pos, byte_pos, word, byte }
                })?;

                utf8_offset += c.encode_utf8(&mut utf8[utf8_offset..]).len();
            }

            self.write_all(&utf8[..utf8_offset])?;
        }

        self.write_all(b"\n")?;
        Ok(())
    }
}

pub trait CharRead {
    fn read_chars(
        &mut self,
        buf: &mut [Word],
        is_terminal: bool,
    ) -> io::Result<()>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidInputCharError {
    pub pos: usize,
    pub ch: char,
}

impl fmt::Display for InvalidInputCharError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl error::Error for InvalidInputCharError {}

impl From<InvalidInputCharError> for io::Error {
    fn from(value: InvalidInputCharError) -> Self {
        io::Error::other(value)
    }
}

impl<R: io::BufRead> CharRead for R {
    fn read_chars(
        &mut self,
        buf: &mut [Word],
        is_terminal: bool,
    ) -> io::Result<()> {
        let mut linebuf = String::new();
        self.read_line(&mut linebuf)?;

        let mut chars = linebuf.char_indices();
        let mut words = buf.iter_mut();

        for word in &mut words {
            let mut bytes = [Byte::MIN; 5];

            for byte in bytes.iter_mut() {
                let next = chars.next();

                if matches!(next, None | Some((_, '\n')))
                    | matches!(next, Some((_, '\r')) if is_terminal)
                {
                    *word = Word::from_sign_bytes(Sign::Plus, bytes);
                    words.into_slice().fill(Word::POS_ZERO);
                    return Ok(());
                }

                let (pos, ch) = next.unwrap();
                *byte = Char::from_unicode_with_replacement(ch)
                    .ok_or(InvalidInputCharError { pos, ch })?
                    .into();
            }

            *word = Word::from_sign_bytes(Sign::Plus, bytes);
        }

        Ok(())
    }
}
