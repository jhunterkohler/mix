use std::error;
use std::fmt;
use std::io;
use std::ops::{Index, IndexMut, Range};

use crate::bin::{Decode, Encode, EncodingError};
use crate::num::{FieldSpec, LocationCounter, Short, Word, impl_int_repr};

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

    /// Converts a [`MemoryAddress`] to `usize`.
    pub const fn to_usize(self) -> usize {
        self.0 as usize
    }

    /// Converts a `usize` to [`MemoryAddress`].
    pub const fn from_usize(value: usize) -> Option<MemoryAddress> {
        if value <= MemoryAddress::MAX.to_usize() {
            Some(MemoryAddress(value as u16))
        } else {
            None
        }
    }

    /// Converts an `usize` to a [`MemoryAddress`], ignoring validity.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `value >
    /// MemoryAddress::MAX.to_usize()`.
    pub const unsafe fn from_usize_unchecked(value: usize) -> MemoryAddress {
        debug_assert!(value <= MemoryAddress::MAX.to_usize());
        MemoryAddress(value as u16)
    }
}

impl_int_repr! {
    int = MemoryAddress,
    repr = usize,
    to_repr = MemoryAddress::to_usize,
    from_repr = MemoryAddress::from_usize,
    from_repr_unchecked = MemoryAddress::from_usize_unchecked,
    from = [u8],
    into = [u16, u32, u128, usize, i16, i32, i128, isize],
    try_from = [u16, u32, u128, usize, i8, i16, i32, i64, i128,
        isize, Short, Word, LocationCounter],
    try_into = [u8, i8],
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
        MemoryAddress::from_usize(u16::decode(r)? as usize)
            .ok_or_else(EncodingError::in_io_error)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InvalidMemoryRangeError(());

impl fmt::Display for InvalidMemoryRangeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("invalid memory range")
    }
}

impl error::Error for InvalidMemoryRangeError {}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct MemoryRange {
    pub start: MemoryAddress,
    pub last: MemoryAddress,
}

impl MemoryRange {
    pub fn new(start: MemoryAddress, last: MemoryAddress) -> Self {
        Self { start, last }
    }

    pub fn from_short_len(start: Short, len: usize) -> Option<Self> {
        Self::from_address_len(start.try_into().ok()?, len)
    }

    pub fn from_address_len(start: MemoryAddress, len: usize) -> Option<Self> {
        Some(Self {
            start,
            last: start
                .to_usize()
                .checked_add(len.checked_sub(1)?)?
                .try_into()
                .ok()?,
        })
    }

    pub const fn len(&self) -> usize {
        let start = self.start.to_usize();
        let last = self.last.to_usize();

        if last < start { 0 } else { last - start + 1 }
    }

    pub const fn is_empty(&self) -> bool {
        self.last.to_usize() < self.start.to_usize()
    }

    pub const fn is_overlapping(&self, other: &MemoryRange) -> bool {
        let r1 = self.to_range_usize();
        let r2 = other.to_range_usize();
        r1.start < r2.end && r2.start < r1.end
    }

    pub(crate) const fn to_range_usize(&self) -> Range<usize> {
        let start = self.start.to_usize();
        let end = start + self.len();
        start..end
    }

    fn is_valid(start: MemoryAddress, len: usize) -> bool {
        if let Some(sum) = start.to_usize().checked_add(len) {
            sum <= Memory::LEN
        } else {
            false
        }
    }
}

impl From<MemoryAddress> for MemoryRange {
    fn from(value: MemoryAddress) -> Self {
        MemoryRange::new(value, value)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Memory {
    data: Box<[Word; Memory::LEN]>,
}

impl Memory {
    pub const LEN: usize = 4000;

    pub fn new() -> Self {
        Self { data: unsafe { Box::new_zeroed().assume_init() } }
    }

    pub fn as_slice(&self) -> &[Word] {
        self.data.as_slice()
    }

    pub fn as_mut_slice(&mut self) -> &mut [Word] {
        self.data.as_mut_slice()
    }

    pub fn reset(&mut self) {
        self.data.fill(Word::POS_ZERO);
    }

    pub fn load<F: Into<Option<FieldSpec>>>(
        &self,
        address: MemoryAddress,
        field_spec: F,
    ) -> Word {
        match field_spec.into() {
            Some(spec) => self[address].with_load(spec),
            None => self[address],
        }
    }

    pub fn store<F: Into<Option<FieldSpec>>>(
        &mut self,
        address: MemoryAddress,
        value: Word,
        field_spec: F,
    ) {
        let dest = &mut self[address];

        match field_spec.into() {
            Some(spec) => *dest = dest.with_store(value, spec),
            None => *dest = value,
        }
    }
}

impl Default for Memory {
    fn default() -> Self {
        Memory::new()
    }
}

impl Index<MemoryAddress> for Memory {
    type Output = Word;

    fn index(&self, index: MemoryAddress) -> &Self::Output {
        unsafe { self.data.get_unchecked(usize::from(index)) }
    }
}

impl IndexMut<MemoryAddress> for Memory {
    fn index_mut(&mut self, index: MemoryAddress) -> &mut Self::Output {
        unsafe { self.data.get_unchecked_mut(usize::from(index)) }
    }
}

impl Index<MemoryRange> for Memory {
    type Output = [Word];

    fn index(&self, index: MemoryRange) -> &Self::Output {
        unsafe { self.data.get_unchecked(index.to_range_usize()) }
    }
}

impl IndexMut<MemoryRange> for Memory {
    fn index_mut(&mut self, index: MemoryRange) -> &mut Self::Output {
        unsafe { self.data.get_unchecked_mut(index.to_range_usize()) }
    }
}
