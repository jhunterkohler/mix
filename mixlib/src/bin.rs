//! A minimal binary serialization format.
//!
//! The serialization/deserialization usage is internal for storing programs
//! on-disk. The only public facing member here [`EncodingError`] which may
//! be returned on decoding operations contained by a [`std::io::Error`].

use std::collections::HashMap;
use std::error::Error;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::hash::Hash;
use std::io;
use std::mem;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};

// `Encode` and `Decode` define a simple, length-prefixed little-endian
// binary encoding for the types used in mixlib's on-disk formats.
// Multi-byte integers are written least-significant byte first; variable-
// length collections are written as a `usize` length followed by their
// elements.

/// An upper bound for the size of any decoded collection. This could prevent
/// allocation panics in the case of parsing bad inputs.
const MAX_COLLECTION_SIZE: usize = 32000;

/// Types that can be written in this module's binary format.
pub(crate) trait Encode {
    /// Writes `self` to `w` in this module's binary format.
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()>;
}

/// Types that can be read from this module's binary format.
pub(crate) trait Decode: Sized {
    /// Reads a value from `r`, previously written by [`Encode::encode`].
    fn decode<R: io::Read>(r: R) -> io::Result<Self>;
}

/// Error returned when decoding encounters malformed or truncated input.
#[derive(Clone, Copy, Debug)]
pub struct EncodingError;

impl EncodingError {
    /// Inspects `e` and, if its kind is [`io::ErrorKind::UnexpectedEof`],
    /// replaces it with an [`EncodingError`]. Useful for mapping the error
    /// from [`io::Read::read_exact`], as done in the integer [`Decode`]
    /// impls.
    pub(crate) fn replace_unexpected_eof(e: io::Error) -> io::Error {
        match e.kind() {
            io::ErrorKind::UnexpectedEof => io::Error::other(EncodingError),
            _ => e,
        }
    }
}

impl fmt::Display for EncodingError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("invalid encoding")
    }
}

impl Error for EncodingError {}

/// Encodes each element in order. The length is fixed by `N`, so unlike
/// slices, no length prefix is written.
impl<T: Encode, const N: usize> Encode for [T; N] {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.iter().try_for_each(|elem| elem.encode(&mut w))
    }
}

/// Incremental initialization guard for arrays.
struct ArrayGuard<'a, T> {
    /// Array to be initialized.
    buf: &'a mut [MaybeUninit<T>],
    /// Number of initialized elements.
    init: usize,
}

impl<T> ArrayGuard<'_, T> {
    /// Push `value` to back of uninitialized array.
    unsafe fn push_unchecked(&mut self, value: T) {
        unsafe {
            self.buf.get_unchecked_mut(self.init).write(value);
            self.init = self.init.unchecked_add(1);
        }
    }
}

impl<T> Drop for ArrayGuard<'_, T> {
    fn drop(&mut self) {
        unsafe { self.buf[..self.init].assume_init_drop() };
    }
}

/// Decodes `N` elements in order, as written by the [`Encode`] impl for
/// `[T; N]`.
impl<T: Decode, const N: usize> Decode for [T; N] {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        let mut buf: [MaybeUninit<T>; N] =
            [const { MaybeUninit::uninit() }; N];
        let mut guard = ArrayGuard { buf: &mut buf, init: 0 };

        for _ in 0..N {
            unsafe { guard.push_unchecked(T::decode(&mut r)?) };
        }

        // Ensure guard's destructor does not run.
        mem::forget(guard);

        // SAFETY: MaybeUninit<T> guarantees same ABI as T. Cannot use regular
        // transmute since the types are dependent.
        unsafe { Ok(mem::transmute_copy(&buf)) }
    }
}

/// Encodes as a `usize` length followed by each element in order.
impl<T: Encode> Encode for [T] {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.len().encode(&mut w)?;
        self.iter().try_for_each(|elem| elem.encode(&mut w))
    }
}

/// Implement encoding for all regular integer types, as fixed-width
/// little-endian bytes.
macro_rules! impl_int_encoding {
    ($($t:ty),*) => {
        $(
            impl Encode for $t {
                fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
                    w.write_all(&self.to_le_bytes())
                }
            }

            impl Decode for $t {
                fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
                    let mut buf = [0u8; size_of::<Self>()];
                    r.read_exact(&mut buf)
                        .map_err(EncodingError::replace_unexpected_eof)?;
                    Ok(Self::from_le_bytes(buf))
                }
            }
        )*
    };
}

impl_int_encoding!(
    u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
);

/// Encodes as a single byte, `0` or `1`.
impl Encode for bool {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        (*self as u8).encode(w)
    }
}

/// Decodes a single byte written by the [`Encode`] impl, erroring on any
/// value other than `0` or `1`.
impl Decode for bool {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        bool::try_from(u8::decode(r)?)
            .map_err(|_| io::Error::other(EncodingError))
    }
}

/// Encodes as a `bool` tag (`true` for `Some`) followed by the value, if
/// present.
impl<T: Encode> Encode for Option<T> {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.is_some().encode(&mut w)?;

        if let Some(value) = self {
            value.encode(&mut w)?;
        }

        Ok(())
    }
}

/// Decodes the tagged layout written by the [`Encode`] impl.
impl<T: Decode> Decode for Option<T> {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        match bool::decode(&mut r)? {
            true => Ok(Some(T::decode(&mut r)?)),
            false => Ok(None),
        }
    }
}

/// Encodes like `[T]`: a `usize` length followed by each element in order.
impl<T: Encode> Encode for Vec<T> {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.as_slice().encode(w)
    }
}

/// Decodes the layout written by the [`Encode`] impl.
///
/// # Errors
///
/// Returns an [`EncodingError`] if the encoded length exceeds
/// [`MAX_COLLECTION_SIZE`], to avoid an unbounded allocation on malformed
/// input.
impl<T: Decode> Decode for Vec<T> {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        let len = usize::decode(&mut r)?;
        if len <= MAX_COLLECTION_SIZE {
            let mut dest = Vec::with_capacity(len);
            for _ in 0..len {
                dest.push(T::decode(&mut r)?);
            }
            Ok(dest)
        } else {
            Err(io::Error::other(EncodingError))
        }
    }
}

/// Encodes as a `usize` length followed by each key/value pair, in
/// iteration order.
impl<K: Encode, V: Encode> Encode for HashMap<K, V> {
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        self.len().encode(&mut w)?;
        self.iter().try_for_each(|(k, v)| {
            k.encode(&mut w)?;
            v.encode(&mut w)
        })
    }
}

/// Decodes the layout written by the [`Encode`] impl.
///
/// # Errors
///
/// Returns an [`EncodingError`] if the encoded length exceeds
/// [`MAX_COLLECTION_SIZE`], or if a key appears more than once.
impl<K: Decode + Hash + Eq, V: Decode> Decode for HashMap<K, V> {
    fn decode<R: io::Read>(mut r: R) -> io::Result<Self> {
        let len = usize::decode(&mut r)?;
        if len <= MAX_COLLECTION_SIZE {
            let mut dest = HashMap::with_capacity(len);

            for _ in 0..len {
                let k = K::decode(&mut r)?;
                let v = V::decode(&mut r)?;

                // Error on duplicate keys.
                if dest.insert(k, v).is_some() {
                    return Err(io::Error::other(EncodingError));
                }
            }

            Ok(dest)
        } else {
            Err(io::Error::other(EncodingError))
        }
    }
}

/// Encodes as its UTF-8 bytes: a `usize` length followed by the bytes
/// themselves.
impl Encode for str {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.as_bytes().encode(w)
    }
}

/// Encodes like [`str`].
impl Encode for String {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.as_str().encode(w)
    }
}

/// Decodes the byte layout written by the [`Encode`] impl.
///
/// # Errors
///
/// Returns an [`EncodingError`] if the decoded bytes are not valid UTF-8.
impl Decode for String {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        String::from_utf8(Vec::<u8>::decode(r)?)
            .map_err(|_| io::Error::other(EncodingError))
    }
}

/// Encodes as a `usize` length followed by platform-native code units: UTF-16
/// (`u16`) elements on Windows, raw (`u8`) bytes on Unix and WASI.
///
/// The encoding is platform-dependent, so data encoded on one platform is
/// not guaranteed to decode correctly on another.
impl Encode for OsStr {
    #[allow(unused_mut)]
    fn encode<W: io::Write>(&self, mut w: W) -> io::Result<()> {
        cfg_select! {
            windows => {
                use std::os::windows::ffi::OsStrExt;
                self.encode_wide().count().encode(&mut w)?;
                self.encode_wide().try_for_each(|elem| elem.encode(&mut w))
            }
            unix => {
                use std::os::unix::ffi::OsStrExt;
                self.as_bytes().encode(w)
            }
            target_os = "wasi" => {
                use std::os::wasi::ffi::OsStrExt;
                self.as_bytes().encode(w)
            }
        }
    }
}

/// Encodes like [`OsStr`].
impl Encode for OsString {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.as_os_str().encode(w)
    }
}

/// Decodes the platform-native layout written by the [`Encode`] impl for
/// [`OsStr`].
impl Decode for OsString {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        cfg_select! {
            windows => {
                use std::os::windows::ffi::OsStringExt;
                Ok(OsString::from_wide(Vec::decode(r)?))
            }
            unix => {
                use std::os::unix::ffi::OsStringExt;
                Ok(OsString::from_vec(Vec::decode(r)?))
            }
            target_os = "wasi" => {
                use std::os::wasi::ffi::OsStringExt;
                Ok(OsString::from_vec(Vec::decode(r)?))
            }
        }
    }
}

/// Encodes like [`OsStr`].
impl Encode for Path {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.as_os_str().encode(w)
    }
}

/// Encodes like [`OsStr`].
impl Encode for PathBuf {
    fn encode<W: io::Write>(&self, w: W) -> io::Result<()> {
        self.as_os_str().encode(w)
    }
}

/// Decodes the layout written by the [`Encode`] impl for [`OsStr`].
impl Decode for PathBuf {
    fn decode<R: io::Read>(r: R) -> io::Result<Self> {
        Ok(PathBuf::from(OsString::decode(r)?))
    }
}
