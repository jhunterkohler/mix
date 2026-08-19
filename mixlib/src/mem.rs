use std::error;
use std::fmt;
use std::io;
use std::ops::Range;
use std::ops::RangeInclusive;
use std::ops::{Index, IndexMut};

use crate::bin::{Decode, Encode, EncodingError};
use crate::num::{LocationCounter, Short, Word, impl_int_repr};

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
    start: MemoryAddress,
    len: u16,
}

impl MemoryRange {
    pub const fn try_new(
        start: MemoryAddress,
        len: usize,
    ) -> Result<MemoryRange, InvalidMemoryRangeError> {
        if Self::is_valid(start, len) {
            Ok(unsafe { MemoryRange::new_unchecked(start, len) })
        } else {
            Err(InvalidMemoryRangeError(()))
        }
    }

    pub const unsafe fn new_unchecked(
        start: MemoryAddress,
        len: usize,
    ) -> MemoryRange {
        debug_assert!(Self::is_valid(start, len));
        MemoryRange { start, len: len as u16 }
    }

    pub const fn start(&self) -> MemoryAddress {
        self.start
    }

    pub const fn len(&self) -> usize {
        self.len as usize
    }

    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn usize_range(&self) -> Range<usize> {
        let start = self.start.to_usize();
        let end = start + self.len as usize;
        start..end
    }

    const fn is_valid(start: MemoryAddress, len: usize) -> bool {
        match start.to_usize().checked_add(len) {
            Some(sum) => sum <= Memory::LEN,
            None => false,
        }
    }
}

impl From<RangeInclusive<MemoryAddress>> for MemoryRange {
    fn from(value: RangeInclusive<MemoryAddress>) -> Self {
        let start = *value.start();
        let len = value.end().to_usize().saturating_sub(start.to_usize());

        unsafe { MemoryRange::new_unchecked(start, len) }
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
        unsafe { self.data.get_unchecked(index.usize_range()) }
    }
}

impl IndexMut<MemoryRange> for Memory {
    fn index_mut(&mut self, index: MemoryRange) -> &mut Self::Output {
        unsafe { self.data.get_unchecked_mut(index.usize_range()) }
    }
}

impl Default for Memory {
    fn default() -> Self {
        Memory::new()
    }
}

// use std::cell::UnsafeCell;
// use std::error;
// use std::fmt;
// use std::ptr;
// use std::range::Range;
// use std::rc::Rc;

// use crate::num::FieldSpec;
// use crate::num::MemoryAddress;
// use crate::num::Word;

// #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
// pub enum MemoryErrorKind {
//     OutOfBounds,
//     BorrowConflict,
// }

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct MemoryError {
//     kind: MemoryErrorKind,
// }

// impl MemoryError {
//     pub fn kind(&self) -> &MemoryErrorKind {
//         &self.kind
//     }
// }

// impl fmt::Display for MemoryError {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         match self.kind {
//             MemoryErrorKind::OutOfBounds => {
//                 f.write_str("memory error: out of bounds access")
//             }
//             MemoryErrorKind::BorrowConflict => {
//                 f.write_str("memory error: conflicting borrows")
//             }
//         }
//     }
// }

// impl error::Error for MemoryError {}

// pub type MemoryResult<T> = Result<T, MemoryError>;

// fn ranges_overlap<T: Ord>(r1: Range<T>, r2: Range<T>) -> bool {
//     r1.start < r2.end && r2.start < r1.end
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// struct BorrowInfo {
//     range: Range<u16>,
//     is_exclusive: bool,
// }

// #[derive(Debug)]
// struct BorrowTracker {
//     borrows: UnsafeCell<Vec<BorrowInfo>>,
// }

// impl BorrowTracker {
//     fn new() -> Self {
//         Self { borrows: Default::default() }
//     }

//     fn add(&self, range: Range<u16>, is_exclusive: bool) {
//         let borrows = unsafe { self.borrows.get().as_mut_unchecked() };
//         borrows.push(BorrowInfo { range, is_exclusive });
//     }

//     fn remove(&self, range: Range<u16>) {
//         let borrows = unsafe { self.borrows.get().as_mut_unchecked() };
//         let pos = borrows.iter().position(|info| info.range == range).unwrap();
//         borrows.swap_remove(pos);
//     }

//     fn can_borrow(&self, range: Range<u16>) -> bool {
//         !unsafe { self.borrows.get().as_ref_unchecked() }
//             .iter()
//             .any(|info| info.is_exclusive && ranges_overlap(info.range, range))
//     }

//     fn can_borrow_mut(&self, range: Range<u16>) -> bool {
//         !unsafe { self.borrows.get().as_ref_unchecked() }
//             .iter()
//             .any(|info| ranges_overlap(info.range, range))
//     }
// }

// #[derive(Debug)]
// struct InnerMemory {
//     data: UnsafeCell<[Word; Memory::LEN]>,
//     borrow_tracker: BorrowTracker,
// }

// impl InnerMemory {
//     fn new() -> Rc<Self> {
//         let mut rc = Rc::new_uninit();
//         let raw: *mut Self = Rc::get_mut(&mut rc).unwrap().as_mut_ptr();

//         unsafe {
//             ptr::addr_of_mut!((*raw).data).write_bytes(0, 1);
//             ptr::addr_of_mut!((*raw).borrow_tracker)
//                 .write(BorrowTracker::new());

//             rc.assume_init()
//         }
//     }

//     fn try_load(
//         &self,
//         address: MemoryAddress,
//         field_spec: Option<FieldSpec>,
//     ) -> MemoryResult<Word> {
//         let index = u16::from(address);
//         let range = Range { start: index, end: index + 1 };

//         if self.borrow_tracker.can_borrow(range) {
//             let mut value = unsafe {
//                 self.data.get().cast::<Word>().add(index as usize).read()
//             };

//             if let Some(spec) = field_spec {
//                 value = value.with_load(spec);
//             }

//             Ok(value)
//         } else {
//             Err(MemoryError { kind: MemoryErrorKind::BorrowConflict })
//         }
//     }

//     fn try_store(
//         &self,
//         address: MemoryAddress,
//         value: Word,
//         field_spec: Option<FieldSpec>,
//     ) -> MemoryResult<()> {
//         let index = u16::from(address);
//         let range = Range { start: index, end: index + 1 };

//         if self.borrow_tracker.can_borrow_mut(range) {
//             let dest =
//                 unsafe { self.data.get().cast::<Word>().add(index as usize) };

//             let new_value = if let Some(spec) = field_spec {
//                 unsafe { dest.read() }.with_store(value, spec)
//             } else {
//                 value
//             };

//             unsafe { dest.write(new_value) }
//             Ok(())
//         } else {
//             Err(MemoryError { kind: MemoryErrorKind::BorrowConflict })
//         }
//     }

//     fn try_borrow(
//         self: &Rc<Self>,
//         start: MemoryAddress,
//         len: usize,
//     ) -> MemoryResult<InnerMemoryRef> {
//         let range = self.check_memory_range(start, len)?;

//         if self.borrow_tracker.can_borrow(range) {
//             self.borrow_tracker.add(range, false);
//             Ok(InnerMemoryRef { range, src: self.clone() })
//         } else {
//             Err(MemoryError { kind: MemoryErrorKind::BorrowConflict })
//         }
//     }

//     fn try_borrow_mut(
//         self: &Rc<Self>,
//         start: MemoryAddress,
//         len: usize,
//     ) -> MemoryResult<InnerMemoryRef> {
//         let range = self.check_memory_range(start, len)?;

//         if self.borrow_tracker.can_borrow_mut(range) {
//             self.borrow_tracker.add(range, true);
//             Ok(InnerMemoryRef { range, src: self.clone() })
//         } else {
//             Err(MemoryError { kind: MemoryErrorKind::BorrowConflict })
//         }
//     }

//     fn check_memory_range(
//         &self,
//         start: MemoryAddress,
//         len: usize,
//     ) -> MemoryResult<Range<u16>> {
//         let start = usize::from(start);

//         if let Some(end) = start.checked_add(len)
//             && end <= Memory::LEN
//         {
//             Ok(Range { start: start as u16, end: end as u16 })
//         } else {
//             Err(MemoryError { kind: MemoryErrorKind::OutOfBounds })
//         }
//     }
// }

// #[derive(Debug)]
// pub struct Memory {
//     inner: Rc<InnerMemory>,
// }

// impl Memory {
//     pub const LEN: usize = 4000;

//     pub fn new() -> Self {
//         Self { inner: InnerMemory::new() }
//     }

//     pub fn try_load(
//         &self,
//         address: MemoryAddress,
//         field_spec: Option<FieldSpec>,
//     ) -> MemoryResult<Word> {
//         self.inner.try_load(address, field_spec)
//     }

//     pub fn try_store(
//         &mut self,
//         address: MemoryAddress,
//         value: Word,
//         field_spec: Option<FieldSpec>,
//     ) -> MemoryResult<()> {
//         self.inner.try_store(address, value, field_spec)
//     }

//     pub fn try_borrow(
//         &self,
//         start: MemoryAddress,
//         len: usize,
//     ) -> MemoryResult<MemoryRef> {
//         self.inner.try_borrow(start, len).map(|inner| MemoryRef { inner })
//     }

//     pub fn try_borrow_mut(
//         &mut self,
//         start: MemoryAddress,
//         len: usize,
//     ) -> MemoryResult<MemoryRefMut> {
//         self.inner
//             .try_borrow_mut(start, len)
//             .map(|inner| MemoryRefMut { inner })
//     }
// }

// impl Default for Memory {
//     fn default() -> Self {
//         Memory::new()
//     }
// }

// struct InnerMemoryRef {
//     range: Range<u16>,
//     src: Rc<InnerMemory>,
// }

// impl InnerMemoryRef {
//     fn slice_ptr(&self) -> *mut [Word] {
//         let start = self.range.start as usize;
//         let len = self.range.end as usize - start;
//         let ptr = unsafe { self.src.data.get().cast::<Word>().add(start) };

//         ptr::slice_from_raw_parts_mut(ptr, len)
//     }

//     unsafe fn as_slice(&self) -> &[Word] {
//         unsafe { self.slice_ptr().as_ref_unchecked() }
//     }

//     unsafe fn as_slice_mut(&self) -> &mut [Word] {
//         unsafe { self.slice_ptr().as_mut_unchecked() }
//     }
// }

// impl Drop for InnerMemoryRef {
//     fn drop(&mut self) {
//         self.src.borrow_tracker.remove(self.range)
//     }
// }

// pub struct MemoryRef {
//     inner: InnerMemoryRef,
// }

// impl MemoryRef {
//     pub fn as_slice(&self) -> &[Word] {
//         unsafe { self.inner.as_slice() }
//     }
// }

// pub struct MemoryRefMut {
//     inner: InnerMemoryRef,
// }

// impl MemoryRefMut {
//     pub fn as_slice(&self) -> &[Word] {
//         unsafe { self.inner.as_slice() }
//     }

//     pub fn as_mut_slice(&mut self) -> &mut [Word] {
//         unsafe { self.inner.as_slice_mut() }
//     }
// }
