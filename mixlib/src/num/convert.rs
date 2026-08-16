use std::error::Error;
use std::fmt;

use crate::num::{Byte, LocationCounter, MemoryAddress, Short, Word};

/// An error that can be returned when converting to between integral types.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TryFromIntError(());

impl fmt::Display for TryFromIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("out of range integral type conversion")
    }
}

impl Error for TryFromIntError {}

macro_rules! int_conv {
    (
        main = $main:ty;
        repr = $repr:ty;
        to_repr = $to_repr:ident;
        from_repr = $from_repr:ident;
        from_repr_unchecked = $from_repr_unchecked:ident;
        try_from_T_for_main = $($try_from_T_for_main:ty),*;
        from_T_for_main = $($from_T_for_main:ty),*;
        try_from_main_for_T = $($try_from_main_for_T:ty),*;
        from_main_for_T = $($from_main_for_T:ty),*;
    ) => {
        $(
            impl TryFrom<$try_from_T_for_main> for $main {
                type Error = TryFromIntError;

                fn try_from(
                    value: $try_from_T_for_main
                ) -> Result<Self, Self::Error> {
                    <$repr>::try_from(value)
                        .ok()
                        .and_then(|as_repr| <$main>::$from_repr(as_repr))
                        .ok_or(TryFromIntError(()))
                }
            }
        )*
        $(
            impl From<$from_T_for_main> for $main {
                fn from(value: $from_T_for_main) -> Self {
                    unsafe {
                        <$main>::$from_repr_unchecked(<$repr>::from(value))
                    }
                }
            }
        )*
        $(
            impl TryFrom<$main> for $try_from_main_for_T {
                type Error = TryFromIntError;

                fn try_from(value: $main) -> Result<Self, Self::Error> {
                    <$try_from_main_for_T>::try_from(value.$to_repr())
                        .map_err(|_| TryFromIntError(()))
                }
            }
        )*
        $(
            impl From<$main> for $from_main_for_T {
                fn from(value: $main) -> Self {
                    unsafe {
                        Self::try_from(value.$to_repr()).unwrap_unchecked()
                    }
                }
            }
        )*
    };
}

int_conv! {
    main = Byte;
    repr = u8;
    to_repr = to_u8;
    from_repr = from_u8;
    from_repr_unchecked = from_u8_unchecked;
    try_from_T_for_main = u8, u16, u32, u64, u128, usize, i8, i16, i32, i128,
        isize, Short, Word, MemoryAddress, LocationCounter;
    from_T_for_main = ;
    try_from_main_for_T = ;
    from_main_for_T = u8, u16, u32, u128, usize, i8, i16, i32, i128, isize;
}

int_conv! {
    main = Short;
    repr = i16;
    to_repr = to_i16;
    from_repr = from_i16;
    from_repr_unchecked = from_i16_unchecked;
    try_from_T_for_main = u16, u32, u64, u128, usize, i16, i32, i64, i128,
        isize;
    from_T_for_main = u8, i8, Byte, MemoryAddress, LocationCounter;
    try_from_main_for_T = u8, u16, u32, u64, u128, usize, i8, isize;
    from_main_for_T = i16, i32, i64, i128;
}

int_conv! {
    main = Word;
    repr = i32;
    to_repr = to_i32;
    from_repr = from_i32;
    from_repr_unchecked = from_i32_unchecked;
    try_from_T_for_main = u32, u64, u128, usize, i32, i64, i128, isize;
    from_T_for_main = u8, u16, i8, i16, Byte, MemoryAddress, LocationCounter;
    try_from_main_for_T = u8, u16, u32, u64, u128, usize, i8, i16, isize;
    from_main_for_T = i32, i64, i128;
}

int_conv! {
    main = MemoryAddress;
    repr = u16;
    to_repr = to_u16;
    from_repr = from_u16;
    from_repr_unchecked = from_u16_unchecked;
    try_from_T_for_main = u16, u32, u128, usize, i8, i16, i32, i64, i128,
        isize, Short, Word, LocationCounter;
    from_T_for_main = u8;
    try_from_main_for_T = u8, i8;
    from_main_for_T = u16, u32, u128, usize, i16, i32, i128, isize;
}

int_conv! {
    main = LocationCounter;
    repr = u16;
    to_repr = to_u16;
    from_repr = from_u16;
    from_repr_unchecked = from_u16_unchecked;
    try_from_T_for_main = u16, u32, u128, usize, i8, i16, i32, i64, i128,
        isize, Short, Word;
    from_T_for_main = u8, MemoryAddress;
    try_from_main_for_T = u8, i8;
    from_main_for_T = u16, u32, u128, usize, i16, i32, i128, isize;
}

// Implement From<Short> and TryFrom<Word> manually to preserve signed zeroes.

impl From<Short> for Word {
    fn from(value: Short) -> Self {
        value.zero_extend_to_word()
    }
}

impl TryFrom<Word> for Short {
    type Error = TryFromIntError;

    fn try_from(value: Word) -> Result<Self, Self::Error> {
        const BAD_BITS: u32 = Word::VALUE_MASK & !(Short::VALUE_MASK as u32);

        if value.0 & BAD_BITS != 0 {
            return Err(TryFromIntError(()));
        }

        let sign_bit = (value.mask_sign() >> 18) as u16;

        // Sign bit is cut off by the cast.
        let value_bits = value.0 as u16;

        Ok(Short(sign_bit | value_bits))
    }
}
