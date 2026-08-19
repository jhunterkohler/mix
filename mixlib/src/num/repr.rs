/// For conversions between internal types, only use `from` and `try_from` to
/// avoid duplication.
macro_rules! impl_int_repr {
    (
        int = $IntT:ty,
        repr = $ReprT:ty,
        to_repr = $to_repr:path,
        from_repr = $from_repr:path,
        from_repr_unchecked = $from_repr_unchecked:path,
        from = [$($FromT:ty),*$(,)?],
        into = [$($IntoT:ty),*$(,)?],
        try_from = [$($TryFromT:ty),*$(,)?],
        try_into = [$($TryIntoT:ty),*$(,)?]$(,)?
    ) => {
        $(
            impl From<$FromT> for $IntT {
                fn from(value: $FromT) -> Self {
                    let repr = <$ReprT as From<$FromT>>::from(value);
                    unsafe { $from_repr_unchecked(repr) }
                }
            }
        )*
        $(
            impl From<$IntT> for $IntoT {
                fn from(value: $IntT) -> Self {
                    let repr = $to_repr(value);

                    // We must use `TryFrom` here. There won't always be
                    // `From` implementations since the representation type
                    // may be more permissive than our $int type.
                    unsafe {
                        <$IntoT as TryFrom<$ReprT>>::try_from(repr)
                            .unwrap_unchecked()
                    }
                }
            }
        )*
        $(
            impl TryFrom<$TryFromT> for $IntT {
                type Error = crate::num::TryFromIntError;

                fn try_from(value: $TryFromT) -> Result<Self, Self::Error> {
                    <$ReprT as TryFrom<$TryFromT>>::try_from(value)
                        .ok()
                        .and_then(|repr| $from_repr(repr))
                        .ok_or(crate::num::TryFromIntError(()))
                }
            }
        )*
        $(
            impl TryFrom<$IntT> for $TryIntoT {
                type Error = crate::num::TryFromIntError;

                fn try_from(value: $IntT) -> Result<Self, Self::Error> {
                    let repr = $to_repr(value);

                    <$TryIntoT as TryFrom<$ReprT>>::try_from(repr)
                        .map_err(|_| crate::num::TryFromIntError(()))
                }
            }
        )*
    };
}

pub(crate) use impl_int_repr;
