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
use std::io::{self, BufRead, Read, Seek, SeekFrom, Write};
use std::mem::transmute;

use crate::bin::{Decode, Encode, EncodingError};
use crate::char::Char;
use crate::num::{Byte, Short, Sign, Word};

/// Number of bytes used to encode one [`Word`] in the binary format used by
/// [`Tape`] and [`Disk`]. Block byte offsets are this many times a device's
/// [`DeviceKind::block_size`].
const WORD_ENCODED_LEN: usize = 4;

/// Error returned by [`DeviceUnit::try_from`] when a value is not a valid
/// unit number (i.e., greater than [`DeviceUnit::MAX`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DeviceUnitTryFromError(());

impl fmt::Display for DeviceUnitTryFromError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid device unit number")
    }
}

impl error::Error for DeviceUnitTryFromError {}

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
    type Error = DeviceUnitTryFromError;

    fn try_from(value: usize) -> std::result::Result<Self, Self::Error> {
        DeviceUnit::from_usize(value).ok_or(DeviceUnitTryFromError(()))
    }
}

impl TryFrom<Byte> for DeviceUnit {
    type Error = DeviceUnitTryFromError;

    fn try_from(value: Byte) -> std::result::Result<Self, Self::Error> {
        DeviceUnit::try_from(usize::from(value))
    }
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

    /// Return an error if block size is invalid.
    fn validate_block_size(self, data: &[Word]) -> Result<()> {
        if data.len() == self.block_size() {
            Ok(())
        } else {
            Err(Error::from(ErrorKind::InvalidBlockSize))
        }
    }
}

/// Whether a [`DeviceKind`] transfers binary words or MIX characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DeviceMode {
    /// Whole [`Word`]s in `mixlib`'s binary encoding.
    Word,
    /// MIX characters, five per word, as a line of text.
    Char,
}

/// The kind of error produced by a [`Device`] operation.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorKind {
    /// The data slice passed to [`Device::input`] or [`Device::output`] did
    /// not match the device's [`DeviceKind::block_size`].
    InvalidBlockSize,
    /// A binary word read from a [`Tape`] or [`Disk`] was not validly
    /// encoded.
    InvalidInputWord,
    /// A character read from a character device was not a valid MIX
    /// character.
    InvalidInputChar,
    /// A word byte written to a character device was not a valid MIX
    /// character.
    InvalidOutputChar,
    /// [`Device::input`] is not supported by this device.
    InputUnsupported,
    /// [`Device::output`] is not supported by this device.
    OutputUnsupported,
    /// Any other I/O error.
    Other,
}

impl ErrorKind {
    fn as_str(&self) -> &'static str {
        match self {
            ErrorKind::InvalidBlockSize => "invalid block size",
            ErrorKind::InvalidInputWord => "invalid input word",
            ErrorKind::InvalidInputChar => "invalid input character",
            ErrorKind::InvalidOutputChar => "invalid output character",
            ErrorKind::InputUnsupported => "input unsupported",
            ErrorKind::OutputUnsupported => "output unsupported",
            ErrorKind::Other => "other",
        }
    }
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// The error type for [`Device`] operations.
#[derive(Debug)]
pub struct Error {
    kind: ErrorKind,
    inner: Option<Box<dyn error::Error + Send + Sync>>,
}

impl Error {
    /// Creates an error of the given `kind`, wrapping `e` as its source.
    pub fn new<E>(kind: ErrorKind, e: E) -> Error
    where
        E: Into<Box<dyn error::Error + Send + Sync>>,
    {
        Self { kind, inner: Some(e.into()) }
    }

    /// Creates an [`ErrorKind::Other`] error wrapping `e`.
    pub fn other<E>(e: E) -> Error
    where
        E: Into<Box<dyn error::Error + Send + Sync>>,
    {
        Self { kind: ErrorKind::Other, inner: Some(e.into()) }
    }

    /// Returns the corresponding [`ErrorKind`] for this error.
    pub fn kind(&self) -> ErrorKind {
        self.kind
    }

    /// Returns a reference to the inner error wrapped by this error, if any.
    pub fn get_ref(
        &self,
    ) -> Option<&(dyn error::Error + Send + Sync + 'static)> {
        self.inner.as_deref()
    }

    /// Returns a mutable reference to the inner error wrapped by this error,
    /// if any.
    pub fn get_mut(
        &mut self,
    ) -> Option<&mut (dyn error::Error + Send + Sync + 'static)> {
        self.inner.as_deref_mut()
    }

    /// Consumes this error, returning the inner error it wraps, if any.
    pub fn into_inner(self) -> Option<Box<dyn error::Error + Send + Sync>> {
        self.inner
    }
}

impl From<ErrorKind> for Error {
    fn from(value: ErrorKind) -> Self {
        Error { kind: value, inner: None }
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Self {
        // Unwrap device error if it is one.
        match e.downcast::<Error>() {
            Ok(e) => e,
            Err(e) => Error::other(e),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.inner {
            Some(e) => e.fmt(f),
            None => self.kind.fmt(f),
        }
    }
}

impl error::Error for Error {}

/// A specialized [`Result`](std::result::Result) type for [`Device`]
/// operations.
pub type Result<T> = std::result::Result<T, Error>;

/// A MIX peripheral device.
///
/// Every method here executes synchronously and represents the effect of one
/// `IN`, `OUT`, or `IOC` instruction against this unit; see the
/// [module documentation](self) and Knuth, *TAOCP* Vol. 1, §1.3.1.
pub trait Device {
    /// Returns this device's [`DeviceKind`].
    fn kind(&self) -> DeviceKind;

    /// Performs an `IN` instruction: fills `data` from the device.
    ///
    /// `data.len()` must equal [`DeviceKind::block_size`] for this device's
    /// kind, or [`ErrorKind::InvalidBlockSize`] is returned. `block` carries
    /// the contents of index register `rX`; it is used only by devices whose
    /// transfers are addressed by block number (currently [`Disk`]) and is
    /// ignored otherwise.
    fn input(&mut self, data: &mut [Word], block: Word) -> Result<()>;

    /// Performs an `OUT` instruction: writes `data` to the device.
    ///
    /// See [`Device::input`] for the meaning of `block` and the
    /// [`ErrorKind::InvalidBlockSize`] requirement on `data.len()`.
    fn output(&mut self, data: &[Word], block: Word) -> Result<()>;

    /// Performs an `IOC` instruction, whose effect is device-specific (see
    /// each device's [`Device`] impl). `arg` carries the instruction's
    /// address field `M`; `block` carries `rX`, as in [`Device::input`].
    fn control(&mut self, arg: Short, block: Word) -> Result<()>;

    /// Returns whether the device is ready, i.e., not busy with a previous
    /// operation (as tested by `JRED`/`JBUS`).
    ///
    /// Because every device here completes its work synchronously before
    /// returning from [`Device::input`], [`Device::output`], and
    /// [`Device::control`], this always returns `Ok(true)`.
    fn ready(&self) -> Result<bool>;
}

/// Write words in binary format.
fn write_words(
    kind: DeviceKind,
    mut w: impl Write,
    src: &[Word],
) -> Result<()> {
    kind.validate_block_size(src)?;

    for word in src {
        word.encode(&mut w)?;
    }

    Ok(())
}

/// Read words in binary format.
fn read_words(
    kind: DeviceKind,
    mut r: impl Read,
    dest: &mut [Word],
) -> Result<()> {
    kind.validate_block_size(dest)?;

    for word in dest {
        *word = Word::decode(&mut r).map_err(|e| {
            match e.downcast::<EncodingError>() {
                Ok(_) => Error::from(ErrorKind::InvalidInputWord),
                Err(e) => Error::other(e),
            }
        })?;
    }

    Ok(())
}

/// Write chars in utf8 with newline.
fn write_chars(
    kind: DeviceKind,
    mut w: impl Write,
    src: &[Word],
) -> Result<()> {
    kind.validate_block_size(src)?;

    for word in src {
        let (_, bytes) = word.to_sign_bytes();
        let mut utf8 = [0u8; 5 * Char::MAX_LEN_UTF8];
        let mut utf8_offset = 0;

        for byte in bytes {
            let c = Char::try_from(byte)
                .map_err(|_| Error::from(ErrorKind::InvalidOutputChar))?;

            utf8_offset += c.encode_utf8(&mut utf8[utf8_offset..]).len();
        }

        w.write_all(&utf8[..utf8_offset])?;
    }

    w.write_all(b"\n")?;
    Ok(())
}

/// Take the input char and convert it to a mix byte, or give a device error.
fn input_char_to_mix_byte(c: char) -> Result<Byte> {
    Char::from_unicode_with_replacement(c)
        .ok_or_else(|| Error::from(ErrorKind::InvalidInputChar))
        .map(Into::into)
}

/// Read one line as MIX characters, blank-padding to `dest`'s block size.
///
/// A line ends at `\n`, at EOF, or (for [`DeviceKind::Terminal`] only) at
/// `\r`, matching a typewriter's carriage return. Any words past the end of
/// the line are filled with blanks. Contents of `buf` are not preserved.
fn read_chars(
    kind: DeviceKind,
    mut r: impl BufRead,
    mut dest: &mut [Word],
    buf: &mut String,
) -> Result<()> {
    kind.validate_block_size(dest)?;

    // Prepare line.
    buf.clear();
    r.read_line(buf)?;

    let mut chars = buf.chars();

    while !dest.is_empty() {
        let mut bytes = [Byte::MIN; 5];

        for byte in bytes.iter_mut() {
            let next = chars.next();

            if next.is_none()
                || next == Some('\n')
                || (next == Some('\r') && kind == DeviceKind::Terminal)
            {
                dest[0] = Word::from_sign_bytes(Sign::Plus, bytes);
                dest[1..].fill(Word::POS_ZERO);
                return Ok(());
            }

            *byte = input_char_to_mix_byte(next.unwrap())?;
        }

        dest[0] = Word::from_sign_bytes(Sign::Plus, bytes);
        dest = &mut dest[1..];
    }

    Ok(())
}

/// A magnetic tape unit (device numbers 0-7).
///
/// Tape is addressed sequentially; [`Device::control`]'s `arg` rewinds to
/// the start of the tape (`arg == 0`), or skips `arg` blocks forward
/// (`arg > 0`), or skips `-arg` blocks backward, clipped to the start of the
/// tape (`arg < 0`). `block` is ignored.
pub struct Tape<I: ?Sized> {
    inner: I,
}

impl<I: Read + Write + Seek> Tape<I> {
    /// Creates a new tape device backed by `inner`, initially positioned at
    /// the start of the tape.
    pub fn new(inner: I) -> Tape<I> {
        Self { inner }
    }

    /// Consumes this device, returning the underlying reader/writer.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: Read + Write + Seek + ?Sized> Tape<I> {
    /// Returns a reference to the underlying reader/writer.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying reader/writer.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }
}

impl<I: Read + Write + Seek + ?Sized> Device for Tape<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::Tape
    }

    fn input(&mut self, data: &mut [Word], _block: Word) -> Result<()> {
        read_words(self.kind(), self.get_mut(), data)
    }

    fn output(&mut self, data: &[Word], _block: Word) -> Result<()> {
        write_words(self.kind(), self.get_mut(), data)
    }

    fn control(&mut self, arg: Short, _block: Word) -> Result<()> {
        let byte_offset = i64::from(arg)
            * (self.kind().block_size() * WORD_ENCODED_LEN) as i64;

        // Must handle seeking to negative positions, which the `Seek`
        // trait considers an error.
        if byte_offset == 0
            || (byte_offset < 0
                && self.inner.stream_position()? <= byte_offset.unsigned_abs())
        {
            self.inner.rewind()?;
        } else {
            self.inner.seek_relative(byte_offset)?;
        }

        Ok(())
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

/// A disk or drum unit (device numbers 8-15).
///
/// Transfers are addressed by block, given by `block` (the contents of
/// index register `rX`) on [`Device::input`], [`Device::output`], and
/// [`Device::control`]. `arg` is ignored.
pub struct Disk<I: Read + Write + Seek + ?Sized> {
    inner: I,
}

impl<I: Read + Write + Seek> Disk<I> {
    /// Creates a new disk device backed by `inner`.
    pub fn new(inner: I) -> Disk<I> {
        Self { inner }
    }

    /// Consumes this device, returning the underlying reader/writer.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: Read + Write + Seek + ?Sized> Disk<I> {
    /// Returns a reference to the underlying reader/writer.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying reader/writer.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }

    fn set_block(&mut self, block: Word) -> Result<()> {
        let byte_offset = i64::from(block).unsigned_abs()
            * (self.kind().block_size() * WORD_ENCODED_LEN) as u64;

        self.inner.seek(SeekFrom::Start(byte_offset))?;
        Ok(())
    }
}

impl<I: Read + Write + Seek + ?Sized> Device for Disk<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::Disk
    }

    fn input(&mut self, data: &mut [Word], block: Word) -> Result<()> {
        self.set_block(block)?;
        read_words(self.kind(), self.get_mut(), data)
    }

    fn output(&mut self, data: &[Word], block: Word) -> Result<()> {
        self.set_block(block)?;
        write_words(self.kind(), self.get_mut(), data)
    }

    fn control(&mut self, _arg: Short, block: Word) -> Result<()> {
        self.set_block(block)
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

/// A card reader (device 16).
///
/// Input only; [`Device::output`] returns [`ErrorKind::OutputUnsupported`].
pub struct CardReader<I: BufRead + ?Sized> {
    buf: String,
    inner: I,
}

impl<I: BufRead> CardReader<I> {
    /// Creates a new card reader backed by `inner`.
    pub fn new(inner: I) -> CardReader<I> {
        Self { buf: String::new(), inner }
    }

    /// Consumes this device, returning the underlying reader.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: BufRead + ?Sized> CardReader<I> {
    /// Returns a reference to the underlying reader.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying reader.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }
}

impl<I: BufRead + ?Sized> Device for CardReader<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::CardReader
    }

    fn input(&mut self, data: &mut [Word], _block: Word) -> Result<()> {
        read_chars(self.kind(), &mut self.inner, data, &mut self.buf)
    }

    fn output(&mut self, _data: &[Word], _block: Word) -> Result<()> {
        Err(Error::from(ErrorKind::OutputUnsupported))
    }

    fn control(&mut self, _arg: Short, _block: Word) -> Result<()> {
        Ok(())
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

/// A card punch (device 17).
///
/// Output only; [`Device::input`] returns [`ErrorKind::InputUnsupported`].
pub struct CardPunch<I: Write + ?Sized> {
    inner: I,
}

impl<I: Write> CardPunch<I> {
    /// Creates a new card punch backed by `inner`.
    pub fn new(inner: I) -> CardPunch<I> {
        Self { inner }
    }

    /// Consumes this device, returning the underlying writer.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: Write + ?Sized> CardPunch<I> {
    /// Returns a reference to the underlying writer.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying writer.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }
}

impl<I: Write + ?Sized> Device for CardPunch<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::CardPunch
    }

    fn input(&mut self, _data: &mut [Word], _block: Word) -> Result<()> {
        Err(Error::from(ErrorKind::InputUnsupported))
    }

    fn output(&mut self, data: &[Word], _block: Word) -> Result<()> {
        write_chars(self.kind(), self.get_mut(), data)
    }

    fn control(&mut self, _arg: Short, _block: Word) -> Result<()> {
        Ok(())
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

/// A line printer (device 18).
///
/// Output only; [`Device::input`] returns [`ErrorKind::InputUnsupported`].
/// [`Device::control`] advances to the top of the next page, approximated
/// here by writing a blank line.
pub struct LinePrinter<I: Write + ?Sized> {
    inner: I,
}

impl<I: Write> LinePrinter<I> {
    /// Creates a new line printer backed by `inner`.
    pub fn new(inner: I) -> LinePrinter<I> {
        Self { inner }
    }

    /// Consumes this device, returning the underlying writer.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: Write + ?Sized> LinePrinter<I> {
    /// Returns a reference to the underlying writer.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying writer.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }
}

impl<I: Write + ?Sized> Device for LinePrinter<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::LinePrinter
    }

    fn input(&mut self, _data: &mut [Word], _block: Word) -> Result<()> {
        Err(Error::from(ErrorKind::InputUnsupported))
    }

    fn output(&mut self, data: &[Word], _block: Word) -> Result<()> {
        write_chars(self.kind(), self.get_mut(), data)
    }

    fn control(&mut self, _arg: Short, _block: Word) -> Result<()> {
        self.inner.write_all(b"\n")?;
        Ok(())
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

/// A typewriter terminal (device 19).
///
/// Supports both input and output.
pub struct Terminal<I: BufRead + Write + ?Sized> {
    buf: String,
    inner: I,
}

impl<I: BufRead + Write> Terminal<I> {
    /// Creates a new terminal backed by `inner`.
    pub fn new(inner: I) -> Terminal<I> {
        Self { buf: String::new(), inner }
    }

    /// Consumes this device, returning the underlying reader/writer.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: BufRead + Write + ?Sized> Terminal<I> {
    /// Returns a reference to the underlying reader/writer.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying reader/writer.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }
}

impl<I: BufRead + Write + ?Sized> Device for Terminal<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::Terminal
    }

    fn input(&mut self, data: &mut [Word], _block: Word) -> Result<()> {
        read_chars(self.kind(), &mut self.inner, data, &mut self.buf)
    }

    fn output(&mut self, data: &[Word], _block: Word) -> Result<()> {
        write_chars(self.kind(), &mut self.inner, data)
    }

    fn control(&mut self, _arg: Short, _block: Word) -> Result<()> {
        Ok(())
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

/// A paper tape unit (device 20).
///
/// Supports both input and output. [`Device::control`] rewinds the tape;
/// `arg` and `block` are ignored.
pub struct PaperTape<I: BufRead + Write + Seek + ?Sized> {
    buf: String,
    inner: I,
}

impl<I: BufRead + Write + Seek> PaperTape<I> {
    /// Creates a new paper tape device backed by `inner`, initially
    /// positioned at the start of the tape.
    pub fn new(inner: I) -> PaperTape<I> {
        Self { buf: String::new(), inner }
    }

    /// Consumes this device, returning the underlying reader/writer.
    pub fn into_inner(self) -> I {
        self.inner
    }
}

impl<I: BufRead + Write + Seek + ?Sized> PaperTape<I> {
    /// Returns a reference to the underlying reader/writer.
    pub fn get_ref(&self) -> &I {
        &self.inner
    }

    /// Returns a mutable reference to the underlying reader/writer.
    pub fn get_mut(&mut self) -> &mut I {
        &mut self.inner
    }
}

impl<I: BufRead + Write + Seek + ?Sized> Device for PaperTape<I> {
    fn kind(&self) -> DeviceKind {
        DeviceKind::PaperTape
    }

    fn input(&mut self, data: &mut [Word], _block: Word) -> Result<()> {
        read_chars(self.kind(), &mut self.inner, data, &mut self.buf)
    }

    fn output(&mut self, data: &[Word], _block: Word) -> Result<()> {
        write_chars(self.kind(), self.get_mut(), data)
    }

    fn control(&mut self, _arg: Short, _block: Word) -> Result<()> {
        self.inner.rewind()?;
        Ok(())
    }

    fn ready(&self) -> Result<bool> {
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn word_range(start: i32, len: usize) -> Vec<Word> {
        (0..len as i32).map(|i| Word::try_from(start + i).unwrap()).collect()
    }

    #[test]
    fn error_reports_kind_and_source() {
        let e = Error::new(ErrorKind::InvalidInputChar, "boom");
        assert_eq!(e.kind(), ErrorKind::InvalidInputChar);
        assert!(e.get_ref().is_some());
        assert_eq!(e.to_string(), "boom");

        let e = Error::from(ErrorKind::Other);
        assert_eq!(e.kind(), ErrorKind::Other);
        assert!(e.get_ref().is_none());
        assert_eq!(e.to_string(), "other");
    }

    #[test]
    fn tape_roundtrips_and_validates_block_size() {
        let mut tape = Tape::new(io::Cursor::new(Vec::new()));
        let block = word_range(0, 100);

        tape.output(&block, Word::POS_ZERO).unwrap();
        tape.control(Short::POS_ZERO, Word::POS_ZERO).unwrap();

        let mut buf = vec![Word::POS_ZERO; 100];
        tape.input(&mut buf, Word::POS_ZERO).unwrap();
        assert_eq!(buf, block);
        assert!(tape.ready().unwrap());

        let mut short = vec![Word::POS_ZERO; 3];
        let err = tape.input(&mut short, Word::POS_ZERO).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidBlockSize);
    }

    #[test]
    fn tape_control_skips_whole_blocks() {
        let mut tape = Tape::new(io::Cursor::new(Vec::new()));
        let block_a = word_range(0, 100);
        let block_b = word_range(-100, 100);

        tape.output(&block_a, Word::POS_ZERO).unwrap();
        tape.output(&block_b, Word::POS_ZERO).unwrap();

        // Rewind, then skip forward one whole block to reach block_b.
        tape.control(Short::POS_ZERO, Word::POS_ZERO).unwrap();
        tape.control(Short::try_from(1).unwrap(), Word::POS_ZERO).unwrap();

        let mut buf = vec![Word::POS_ZERO; 100];
        tape.input(&mut buf, Word::POS_ZERO).unwrap();
        assert_eq!(buf, block_b);

        // Skip backward two blocks to land back at the start of block_a.
        tape.control(Short::try_from(-2).unwrap(), Word::POS_ZERO).unwrap();
        tape.input(&mut buf, Word::POS_ZERO).unwrap();
        assert_eq!(buf, block_a);

        // Skipping backward past the start clips to the beginning of tape.
        tape.control(Short::try_from(-100).unwrap(), Word::POS_ZERO).unwrap();
        tape.input(&mut buf, Word::POS_ZERO).unwrap();
        assert_eq!(buf, block_a);
    }

    #[test]
    fn disk_addresses_blocks_by_rx() {
        let mut disk = Disk::new(io::Cursor::new(Vec::new()));
        let block0 = word_range(0, 100);
        let block3 = word_range(-100, 100);

        disk.output(&block0, Word::try_from(0).unwrap()).unwrap();
        disk.output(&block3, Word::try_from(3).unwrap()).unwrap();

        let mut buf = vec![Word::POS_ZERO; 100];
        disk.input(&mut buf, Word::try_from(3).unwrap()).unwrap();
        assert_eq!(buf, block3);

        disk.input(&mut buf, Word::try_from(0).unwrap()).unwrap();
        assert_eq!(buf, block0);
        assert!(disk.ready().unwrap());
    }

    #[test]
    fn disk_control_positions_by_whole_blocks() {
        let mut disk = Disk::new(io::Cursor::new(Vec::new()));
        disk.control(Short::POS_ZERO, Word::try_from(2).unwrap()).unwrap();
        assert_eq!(
            disk.get_ref().position(),
            2 * 100 * WORD_ENCODED_LEN as u64
        );
    }

    #[test]
    fn card_reader_pads_short_line_with_blanks_and_rejects_output() {
        let mut reader = CardReader::new(io::Cursor::new(b"HI\n".to_vec()));
        let mut buf = vec![Word::try_from(-1).unwrap(); 16];

        reader.input(&mut buf, Word::POS_ZERO).unwrap();

        let (sign, bytes) = buf[0].to_sign_bytes();
        assert_eq!(sign, Sign::Plus);
        assert_eq!(bytes[0], Char::CapitalH.into());
        assert_eq!(bytes[1], Char::CapitalI.into());
        assert_eq!(bytes[2], Byte::MIN);
        assert_eq!(bytes[3], Byte::MIN);
        assert_eq!(bytes[4], Byte::MIN);

        for word in &buf[1..] {
            assert_eq!(*word, Word::POS_ZERO);
        }

        let err = reader.output(&[], Word::POS_ZERO).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::OutputUnsupported);
    }

    #[test]
    fn card_punch_writes_chars_ignoring_sign_and_rejects_input() {
        let mut punch = CardPunch::new(io::Cursor::new(Vec::<u8>::new()));
        let mut words = vec![Word::POS_ZERO; 16];
        let mut bytes = [Byte::MIN; 5];
        bytes[0] = Char::CapitalH.into();
        bytes[1] = Char::CapitalI.into();
        words[0] = Word::from_sign_bytes(Sign::Minus, bytes);

        punch.output(&words, Word::POS_ZERO).unwrap();

        let out = punch.into_inner().into_inner();
        assert!(String::from_utf8(out).unwrap().starts_with("HI"));

        let mut punch = CardPunch::new(io::Cursor::new(Vec::<u8>::new()));
        let mut buf = vec![Word::POS_ZERO; 16];
        let err = punch.input(&mut buf, Word::POS_ZERO).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InputUnsupported);
    }

    #[test]
    fn line_printer_input_is_unsupported_with_correct_kind() {
        let mut printer = LinePrinter::new(io::Cursor::new(Vec::<u8>::new()));
        let mut buf = vec![Word::POS_ZERO; 24];
        let err = printer.input(&mut buf, Word::POS_ZERO).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InputUnsupported);
    }

    #[test]
    fn line_printer_control_advances_page() {
        let mut printer = LinePrinter::new(io::Cursor::new(Vec::<u8>::new()));
        printer.control(Short::POS_ZERO, Word::POS_ZERO).unwrap();
        assert_eq!(printer.into_inner().into_inner(), b"\n");
    }

    #[test]
    fn terminal_input_ends_line_at_newline_or_carriage_return() {
        let mut term = Terminal::new(io::Cursor::new(b"HI\r\nBYE\n".to_vec()));
        let mut buf = vec![Word::try_from(-1).unwrap(); 14];

        term.input(&mut buf, Word::POS_ZERO).unwrap();
        let (_, bytes) = buf[0].to_sign_bytes();
        assert_eq!(bytes[0], Char::CapitalH.into());
        assert_eq!(bytes[1], Char::CapitalI.into());
        assert_eq!(bytes[2], Byte::MIN);

        term.input(&mut buf, Word::POS_ZERO).unwrap();
        let (_, bytes) = buf[0].to_sign_bytes();
        assert_eq!(bytes[0], Char::CapitalB.into());
        assert_eq!(bytes[1], Char::CapitalY.into());
        assert_eq!(bytes[2], Char::CapitalE.into());
        assert_eq!(bytes[3], Byte::MIN);

        term.control(Short::POS_ZERO, Word::POS_ZERO).unwrap();
        assert!(term.ready().unwrap());
    }

    #[test]
    fn terminal_output_writes_line() {
        let mut term = Terminal::new(io::Cursor::new(Vec::<u8>::new()));
        let mut words = vec![Word::POS_ZERO; 14];
        let mut bytes = [Byte::MIN; 5];
        bytes[0] = Char::CapitalH.into();
        bytes[1] = Char::CapitalI.into();
        words[0] = Word::from_sign_bytes(Sign::Plus, bytes);

        term.output(&words, Word::POS_ZERO).unwrap();

        let out = term.into_inner().into_inner();
        assert!(String::from_utf8(out).unwrap().starts_with("HI"));
    }

    #[test]
    fn paper_tape_supports_input_and_output() {
        let mut tape = PaperTape::new(io::Cursor::new(b"HI\n".to_vec()));
        let mut buf = vec![Word::try_from(-1).unwrap(); 14];

        tape.input(&mut buf, Word::POS_ZERO).unwrap();
        let (_, bytes) = buf[0].to_sign_bytes();
        assert_eq!(bytes[0], Char::CapitalH.into());
        assert_eq!(bytes[1], Char::CapitalI.into());

        let mut tape = PaperTape::new(io::Cursor::new(Vec::<u8>::new()));
        let mut words = vec![Word::POS_ZERO; 14];
        words[0] = buf[0];
        tape.output(&words, Word::POS_ZERO).unwrap();

        assert!(
            String::from_utf8(tape.get_ref().get_ref().clone())
                .unwrap()
                .starts_with("HI")
        );

        tape.control(Short::POS_ZERO, Word::POS_ZERO).unwrap();
        assert_eq!(tape.get_ref().position(), 0);
        assert!(tape.ready().unwrap());
    }
}
