//! Source positions and ranges.
//!
//! This module defines [`Span`], a byte-offset range used to reference a
//! region of source text.

use std::io;
use std::ops::{Index, IndexMut, Range};

use crate::bin::{Decode, Encode};

/// Span in source file.
///
/// Represents the source between two byte offsets.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    /// The starting byte offset of the span.
    pub start: usize,
    /// The past-end byte offset of the span.
    pub end: usize,
}

impl Span {
    /// Create a new span between `start` and `end`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::source::Span;
    ///
    /// let span = Span::new(123, 456);
    ///
    /// assert_eq!(span.start, 123);
    /// assert_eq!(span.end, 456);
    /// ```
    pub const fn new(start: usize, end: usize) -> Span {
        Span { start, end }
    }

    /// Create an empty span at `pos` with start and end equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::source::Span;
    ///
    /// let span = Span::empty(123);
    ///
    /// assert_eq!(span.start, 123);
    /// assert_eq!(span.end, 123);
    /// ```
    pub const fn empty(pos: usize) -> Span {
        Span::new(pos, pos)
    }

    /// Returns `true` if the span is empty.
    ///
    /// A span is empty if the start is at or past the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::source::Span;
    ///
    /// let empty1 = Span::empty(123);
    /// let empty2 = Span::new(2, 1);
    /// let notempty = Span::new(1, 2);
    ///
    /// assert!(empty1.is_empty());
    /// assert!(empty2.is_empty());
    /// assert!(!notempty.is_empty());
    /// ```
    pub const fn is_empty(self) -> bool {
        self.start >= self.end
    }

    /// Returns the length of the span.
    ///
    /// This returns `0` precisely when [`Span::is_empty`] is true.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::source::Span;
    ///
    /// let empty1 = Span::empty(123);
    /// let empty2 = Span::new(2, 1);
    /// let notempty = Span::new(1, 5);
    ///
    /// assert_eq!(empty1.len(), 0);
    /// assert_eq!(empty2.len(), 0);
    /// assert_eq!(notempty.len(), 4);
    /// ```
    pub const fn len(self) -> usize {
        self.end.saturating_sub(self.start)
    }

    /// Returns a new span replacing start with `new_start`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::source::Span;
    ///
    /// let span = Span::new(1, 2);
    /// let new_span = span.with_start(0);
    ///
    /// assert_eq!(new_span.start, 0);
    /// assert_eq!(new_span.end, 2);
    /// ```
    pub const fn with_start(self, new_start: usize) -> Span {
        Span::new(new_start, self.end)
    }

    /// Returns a new span replacing end with `new_end`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mixlib::source::Span;
    ///
    /// let span = Span::new(1, 2);
    /// let new_span = span.with_end(3);
    ///
    /// assert_eq!(new_span.start, 1);
    /// assert_eq!(new_span.end, 3);
    /// ```
    pub const fn with_end(self, new_end: usize) -> Span {
        Span::new(self.start, new_end)
    }
}

impl Index<Span> for [u8] {
    type Output = [u8];

    fn index(&self, index: Span) -> &Self::Output {
        &self[index.start..index.end]
    }
}

impl IndexMut<Span> for [u8] {
    fn index_mut(&mut self, index: Span) -> &mut Self::Output {
        &mut self[index.start..index.end]
    }
}

impl Index<Span> for str {
    type Output = str;

    fn index(&self, index: Span) -> &Self::Output {
        &self[index.start..index.end]
    }
}

impl IndexMut<Span> for str {
    fn index_mut(&mut self, index: Span) -> &mut Self::Output {
        &mut self[index.start..index.end]
    }
}

impl From<Span> for Range<usize> {
    fn from(span: Span) -> Self {
        span.start..span.end
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Span::new(range.start, range.end)
    }
}

impl Encode for Span {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.start.encode(&mut w)?;
        self.end.encode(&mut w)?;
        Ok(())
    }
}

impl Decode for Span {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        Ok(Span::new(usize::decode(&mut r)?, usize::decode(&mut r)?))
    }
}
