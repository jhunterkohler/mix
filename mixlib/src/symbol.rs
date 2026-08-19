//! MIX symbol utilities

use std::cmp::Ordering;
use std::error::Error;
use std::hash::{Hash, Hasher};
use std::ops::Index;
use std::ops::IndexMut;
use std::slice;
use std::str::FromStr;
use std::{fmt, io};

use crate::bin::{Decode, Encode, EncodingError};

/// An enum describing the type of error that arose during symbol name
/// conversion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbolNameTryFromErrorKind {
    /// The symbol name was empty.
    Empty,
    /// The symbol name was too long.
    TooLong,
    /// No alphabetical characters in the name.
    NoAlpha,
    /// Invalid character encountered in the name.
    BadChar,
    /// The name denotes a local symbol reference: `dH`, `dB`, or `dF` for some
    /// decimal digit `d`.
    LocalSymbol,
}

/// An error than can occur during symbol name conversion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolNameTryFromError {
    kind: SymbolNameTryFromErrorKind,
}

impl SymbolNameTryFromError {
    /// The kind of error that occurred.
    pub fn kind(&self) -> &SymbolNameTryFromErrorKind {
        &self.kind
    }
}

impl fmt::Display for SymbolNameTryFromError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self.kind {
            SymbolNameTryFromErrorKind::Empty => "empty",
            SymbolNameTryFromErrorKind::TooLong => "too long",
            SymbolNameTryFromErrorKind::NoAlpha => "no alphabetic character",
            SymbolNameTryFromErrorKind::BadChar => "bad character",
            SymbolNameTryFromErrorKind::LocalSymbol => "local symbol",
        })
    }
}

impl Error for SymbolNameTryFromError {}

#[derive(Debug, Clone, Copy)]
pub struct SymbolName {
    data: [u8; 10],
    len: u8,
}

impl SymbolName {
    /// Returns the length of `self`.
    ///
    /// ```
    /// use mixlib::symbol::SymbolName;
    ///
    /// let name = SymbolName::from_bytes(b"ABC").unwrap();
    ///
    /// assert_eq!(name.len(), 3);
    /// ```
    pub const fn len(&self) -> usize {
        self.len as usize
    }

    /// Retusn `self` as a byte slice.
    ///
    /// ```
    /// use mixlib::symbol::SymbolName;
    ///
    /// let name = SymbolName::from_bytes(b"ABC").unwrap();
    ///
    /// assert_eq!(name.as_bytes(), b"ABC");
    /// ```
    pub const fn as_bytes(&self) -> &[u8] {
        debug_assert!(self.len <= 10);

        // SAFETY: length is held <= 10 invariant.
        unsafe { slice::from_raw_parts(self.data.as_ptr(), self.len()) }
    }

    /// Return `self` as a string slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::symbol::SymbolName;
    ///
    /// let name = SymbolName::from_bytes(b"ABC").unwrap();
    ///
    /// assert_eq!(name.as_str(), "ABC");
    /// ```
    pub const fn as_str(&self) -> &str {
        debug_assert!(str::from_utf8(self.as_bytes()).is_ok());

        // SAFETY: The bytes should always be valid utf8 since it is a valid
        // mix symbol name.
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }

    /// Creates a symbol name from bytes.
    ///
    /// Returns successfully with a valid non-local symbol name in `src`, or
    /// an error otherwise.
    pub fn from_bytes(
        src: &[u8],
    ) -> Result<SymbolName, SymbolNameTryFromError> {
        Self::check_bytes(src)?;

        // SAFETY: Just checked src valid.
        Ok(unsafe { Self::from_bytes_unchecked(src) })
    }

    /// Creates a symbol name from bytes without error checking.
    ///
    /// # Safety
    ///
    /// The input `src` must be a valid non-local symbol name.
    pub unsafe fn from_bytes_unchecked(src: &[u8]) -> SymbolName {
        debug_assert!(Self::check_bytes(src).is_ok());

        let mut data = [0; 10];
        data[0..src.len()].copy_from_slice(src);
        SymbolName { data, len: src.len() as u8 }
    }

    fn check_bytes(src: &[u8]) -> Result<(), SymbolNameTryFromError> {
        use SymbolNameTryFromErrorKind::*;

        if src.is_empty() {
            Err(SymbolNameTryFromError { kind: Empty })
        } else if !src
            .iter()
            .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit())
        {
            Err(SymbolNameTryFromError { kind: BadChar })
        } else if src.len() > 10 {
            Err(SymbolNameTryFromError { kind: TooLong })
        } else if src.len() == 2
            && src[0].is_ascii_digit()
            && matches!(src[1], b'H' | b'F' | b'B')
        {
            Err(SymbolNameTryFromError { kind: LocalSymbol })
        } else if !src.iter().any(|b| b.is_ascii_uppercase()) {
            Err(SymbolNameTryFromError { kind: NoAlpha })
        } else {
            Ok(())
        }
    }
}

impl PartialEq for SymbolName {
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl Eq for SymbolName {}

impl PartialOrd for SymbolName {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SymbolName {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_bytes().cmp(other.as_bytes())
    }
}

impl Hash for SymbolName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}

impl FromStr for SymbolName {
    type Err = SymbolNameTryFromError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_bytes(s.as_bytes())
    }
}

impl TryFrom<&str> for SymbolName {
    type Error = SymbolNameTryFromError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::from_bytes(value.as_bytes())
    }
}

impl TryFrom<&[u8]> for SymbolName {
    type Error = SymbolNameTryFromError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Self::from_bytes(value)
    }
}

impl fmt::Display for SymbolName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl Encode for SymbolName {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.len.encode(&mut w)?;
        w.write_all(self.as_bytes())
    }
}

impl Decode for SymbolName {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        let len = u8::decode(&mut r)? as usize;
        if len < 1 || len > 10 {
            return Err(EncodingError::in_io_error());
        }

        let mut buf = [0; 10];
        r.read_exact(&mut buf[0..len])
            .map_err(EncodingError::replace_unexpected_eof)?;

        SymbolName::from_bytes(&buf[0..len])
            .map_err(|_| EncodingError::in_io_error())
    }
}

/// The index of a local symbol.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolIndex(u8);

impl SymbolIndex {
    /// Minimum symbol index. Equal to 1.
    pub const MIN: SymbolIndex = SymbolIndex(0);

    /// Maximum symbol index. Equal to 9.
    pub const MAX: SymbolIndex = SymbolIndex(9);

    /// Create a symbol index from `usize`.
    pub const fn from_usize(index: usize) -> Option<SymbolIndex> {
        if index < 10 { Some(SymbolIndex(index as u8)) } else { None }
    }

    /// Crate a symbol index from `usize` without error checking.
    ///
    /// # Safety
    ///
    /// It must be that `index` is a valid symbol index: 0 &le; index &le; 9.
    pub const unsafe fn from_usize_unchecked(index: usize) -> SymbolIndex {
        debug_assert!(index < 10);
        SymbolIndex(index as u8)
    }

    /// Convert symbol index to `usize`.
    pub const fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl<T> Index<SymbolIndex> for [T] {
    type Output = T;

    fn index(&self, index: SymbolIndex) -> &Self::Output {
        &self[index.to_usize()]
    }
}

impl<T> IndexMut<SymbolIndex> for [T] {
    fn index_mut(&mut self, index: SymbolIndex) -> &mut Self::Output {
        &mut self[index.to_usize()]
    }
}

impl From<SymbolIndex> for usize {
    fn from(value: SymbolIndex) -> Self {
        value.to_usize()
    }
}

/// Error that occurs when converting and invalid symbol index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolIndexTryFromError(());

impl fmt::Display for SymbolIndexTryFromError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("invalid symbol index")
    }
}

impl Error for SymbolIndexTryFromError {}

impl TryFrom<usize> for SymbolIndex {
    type Error = SymbolIndexTryFromError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        Self::from_usize(value).ok_or(SymbolIndexTryFromError(()))
    }
}

impl fmt::Display for SymbolIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Encode for SymbolIndex {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.0.encode(w)
    }
}

impl Decode for SymbolIndex {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        let repr = u8::decode(r)?;
        if repr < 10 {
            Ok(Self(repr))
        } else {
            Err(EncodingError::in_io_error())
        }
    }
}

/// A MIX symbol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum Symbol {
    /// A local symbol, with its index.
    Local(SymbolIndex),
    /// A non-local symbol, with its name.
    NonLocal(SymbolName),
}

impl From<SymbolIndex> for Symbol {
    fn from(value: SymbolIndex) -> Self {
        Symbol::Local(value)
    }
}

impl From<SymbolName> for Symbol {
    fn from(value: SymbolName) -> Self {
        Symbol::NonLocal(value)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Symbol::Local(index) => index.fmt(f),
            Symbol::NonLocal(name) => name.fmt(f),
        }
    }
}

impl Encode for Symbol {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        match self {
            Symbol::Local(index) => {
                true.encode(&mut w)?;
                index.encode(&mut w)?;
            }
            Symbol::NonLocal(name) => {
                false.encode(&mut w)?;
                name.encode(&mut w)?;
            }
        }
        Ok(())
    }
}

impl Decode for Symbol {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        let is_local = bool::decode(&mut r)?;
        if is_local {
            Ok(Symbol::Local(SymbolIndex::decode(r)?))
        } else {
            Ok(Symbol::NonLocal(SymbolName::decode(r)?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn symbol_name_from_bytes_ok() {
        for s in ["A", "A1", "1C", "ABCDEFGHIJ"] {
            assert_eq!(SymbolName::from_str(s).unwrap().as_str(), s);
        }
    }

    #[test]
    fn symbol_name_from_bytes_err_empty() {
        assert_eq!(
            SymbolName::from_bytes(b""),
            Err(SymbolNameTryFromError {
                kind: SymbolNameTryFromErrorKind::Empty
            })
        );
    }

    #[test]
    fn symbol_name_from_bytes_err_bad_char() {
        assert_eq!(
            SymbolName::from_bytes("Σ".as_bytes()),
            Err(SymbolNameTryFromError {
                kind: SymbolNameTryFromErrorKind::BadChar
            })
        );
    }

    #[test]
    fn symbol_name_from_bytes_err_too_long() {
        assert_eq!(
            SymbolName::from_bytes(b"ABCDEFGHIJK"),
            Err(SymbolNameTryFromError {
                kind: SymbolNameTryFromErrorKind::TooLong
            })
        );
    }

    #[test]
    fn symbol_name_from_byte_err_local_symbol() {
        assert_eq!(
            SymbolName::from_bytes(b"1B"),
            Err(SymbolNameTryFromError {
                kind: SymbolNameTryFromErrorKind::LocalSymbol
            })
        );
    }

    #[test]
    fn symbol_name_from_byte_err_no_alpha() {
        assert_eq!(
            SymbolName::from_bytes(b"12345"),
            Err(SymbolNameTryFromError {
                kind: SymbolNameTryFromErrorKind::NoAlpha
            })
        );
    }
}
