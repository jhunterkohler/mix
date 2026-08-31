use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote_spanned};
use syn::{
    Error, LitInt, Result, Token,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

use crate::path::MixlibPath;

struct NoSuffixInt {
    lit: LitInt,
}

impl Parse for NoSuffixInt {
    fn parse(input: ParseStream) -> Result<Self> {
        let lit: LitInt = input.parse()?;

        if lit.suffix().is_empty() {
            Ok(Self { lit })
        } else {
            Err(Error::new_spanned(lit, "integer suffixes are unsupported"))
        }
    }
}

pub enum SignLit {
    Plus(Token![+]),
    Minus(Token![-]),
}

impl SignLit {
    fn span(&self) -> proc_macro2::Span {
        match self {
            SignLit::Plus(token) => token.span,
            SignLit::Minus(token) => token.span,
        }
    }
}

impl Parse for SignLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(Token![+]) {
            input.parse().map(SignLit::Plus)
        } else if lookahead.peek(Token![-]) {
            input.parse().map(SignLit::Minus)
        } else {
            Err(lookahead.error())
        }
    }
}

impl ToTokens for SignLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let stream = match self {
            SignLit::Plus(plus) => {
                let span = plus.span;
                let path = MixlibPath::new_spanned(span);
                quote_spanned! { span => #path::num::Sign::Plus }
            }
            SignLit::Minus(minus) => {
                let span = minus.span;
                let path = MixlibPath::new_spanned(span);
                quote_spanned! { span => #path::num::Sign::Minus }
            }
        };

        tokens.extend(stream);
    }
}

const BYTE_MAX: i128 = 63;
const BYTE_MIN: i128 = 0;
const SHORT_MAX: i128 = (1 << 12) - 1;
const SHORT_MIN: i128 = -SHORT_MAX;
const WORD_MAX: i128 = (1 << 30) - 1;
const WORD_MIN: i128 = -WORD_MAX;

fn parse_ranged_int(
    input: ParseStream,
    name: &str,
    min: i128,
    max: i128,
) -> Result<LitInt> {
    let NoSuffixInt { lit } = input.parse()?;
    // This value can't actually be negative as signs aren't included in the
    // `LitInt` syntax.
    let val: i128 = lit.base10_parse()?;

    if !(min..=max).contains(&val) {
        Err(Error::new_spanned(
            lit,
            format!(
                "literal value '{val}' out of range of {name} ({min}..={max})"
            ),
        ))
    } else {
        Ok(lit)
    }
}

pub struct ByteLit {
    lit: LitInt,
}

impl Parse for ByteLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let lit = parse_ranged_int(input, "MIX byte", BYTE_MIN, BYTE_MAX)?;

        Ok(Self { lit })
    }
}

impl ByteLit {
    fn span(&self) -> Span {
        self.lit.span()
    }
}

impl ToTokens for ByteLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.lit.span();
        let path = MixlibPath::new_spanned(span);
        let lit = &self.lit;

        let stream = quote_spanned! {
            span => const { #path::num::Byte::from_u8(#lit).unwrap() }
        };

        tokens.extend(stream);
    }
}

pub struct ShortIntLit {
    signlit: Option<SignLit>,
    lit: LitInt,
}

impl Parse for ShortIntLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let signlit = if input.peek(Token![+]) || input.peek(Token![-]) {
            Some(input.parse()?)
        } else {
            None
        };

        let lit = parse_ranged_int(input, "MIX short", SHORT_MIN, SHORT_MAX)?;

        Ok(Self { signlit, lit })
    }
}

impl ToTokens for ShortIntLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.lit.span();
        let lit = &self.lit;
        let path = MixlibPath::new_spanned(span);

        let sign = if let Some(signlit) = self.signlit.as_ref() {
            signlit.to_token_stream()
        } else {
            quote_spanned! { span => #path::num::Sign::Plus }
        };

        let stream = quote_spanned! {
            span => const {
                #path::num::Short::from_sign_u16(#sign, #lit).unwrap()
            }
        };

        tokens.extend(stream);
    }
}

pub struct WordIntLit {
    signlit: Option<SignLit>,
    lit: LitInt,
}

impl Parse for WordIntLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let signlit = if input.peek(Token![+]) || input.peek(Token![-]) {
            Some(input.parse()?)
        } else {
            None
        };

        let lit = parse_ranged_int(input, "MIX word", WORD_MIN, WORD_MAX)?;

        Ok(Self { signlit, lit })
    }
}

impl ToTokens for WordIntLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.lit.span();
        let lit = &self.lit;
        let path = MixlibPath::new_spanned(span);

        let sign = if let Some(signlit) = self.signlit.as_ref() {
            signlit.to_token_stream()
        } else {
            quote_spanned! { span => #path::num::Sign::Plus }
        };

        let stream = quote_spanned! {
            span => const {
                #path::num::Word::from_sign_u32(#sign, #lit).unwrap()
            }
        };

        tokens.extend(stream);
    }
}

struct ByteLitList<const N: usize> {
    parts: Punctuated<ByteLit, Token![,]>,
}

impl<const N: usize> Parse for ByteLitList<N> {
    fn parse(input: ParseStream) -> Result<Self> {
        let parts: Punctuated<ByteLit, Token![,]> =
            Punctuated::parse_terminated(input)?;

        if parts.len() == N {
            Ok(Self { parts })
        } else {
            let span = parts
                .first()
                .map(ByteLit::span)
                .unwrap_or_else(Span::call_site);

            Err(Error::new(span, format!("expected {N} bytes")))
        }
    }
}

impl<const N: usize> ToTokens for ByteLitList<N> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.parts.to_tokens(tokens)
    }
}

struct SignedByteLitList<const N: usize> {
    sign: SignLit,
    sep: Token![,],
    parts: ByteLitList<N>,
}

impl<const N: usize> Parse for SignedByteLitList<N> {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self {
            sign: input.parse()?,
            sep: input.parse()?,
            parts: input.parse()?,
        })
    }
}

impl<const N: usize> ToTokens for SignedByteLitList<N> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.sign.span();
        let sign = &self.sign;
        let sep = &self.sep;
        let parts = &self.parts;

        let stream = quote_spanned! { span => #sign #sep [#parts] };

        tokens.extend(stream);
    }
}

pub struct ShortBytesLit {
    list: SignedByteLitList<2>,
}

impl Parse for ShortBytesLit {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self { list: input.parse()? })
    }
}

impl ToTokens for ShortBytesLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.list.sign.span();
        let path = MixlibPath::new_spanned(span);
        let list = &self.list;

        let stream = quote_spanned! {
            span => const { #path::num::Short::from_sign_bytes(#list) }
        };

        tokens.extend(stream);
    }
}

pub enum ShortLit {
    Bytes(ShortBytesLit),
    Int(ShortIntLit),
}

impl Parse for ShortLit {
    fn parse(input: ParseStream) -> Result<Self> {
        if (input.peek(Token![-]) || input.peek(Token![+]))
            && input.peek2(Token![,])
        {
            input.parse().map(ShortLit::Bytes)
        } else {
            input.parse().map(ShortLit::Int)
        }
    }
}

impl ToTokens for ShortLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            ShortLit::Bytes(bytes) => bytes.to_tokens(tokens),
            ShortLit::Int(int) => int.to_tokens(tokens),
        }
    }
}

pub struct WordBytesLit {
    list: SignedByteLitList<5>,
}

impl Parse for WordBytesLit {
    fn parse(input: ParseStream) -> Result<Self> {
        Ok(Self { list: input.parse()? })
    }
}

impl ToTokens for WordBytesLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.list.sign.span();
        let path = MixlibPath::new_spanned(span);
        let list = &self.list;

        let stream = quote_spanned! {
            span => const { #path::num::Word::from_sign_bytes(#list) }
        };

        tokens.extend(stream);
    }
}

pub enum WordLit {
    Bytes(WordBytesLit),
    Int(WordIntLit),
}

impl Parse for WordLit {
    fn parse(input: ParseStream) -> Result<Self> {
        if (input.peek(Token![-]) || input.peek(Token![+]))
            && input.peek2(Token![,])
        {
            input.parse().map(WordLit::Bytes)
        } else {
            input.parse().map(WordLit::Int)
        }
    }
}

impl ToTokens for WordLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            WordLit::Bytes(bytes) => bytes.to_tokens(tokens),
            WordLit::Int(int) => int.to_tokens(tokens),
        }
    }
}

fn field_parts_valid(left: i128, right: i128) -> bool {
    0 <= left && left <= right && right <= 5
}

pub struct FieldPartsLit {
    left: LitInt,
    sep: Token![:],
    right: LitInt,
}

impl FieldPartsLit {
    fn finish_parse(input: ParseStream, left: LitInt) -> Result<Self> {
        let sep: Token![:] = input.parse()?;
        let NoSuffixInt { lit: right } = input.parse()?;
        let left_val = left.base10_parse()?;
        let right_val = right.base10_parse()?;

        if field_parts_valid(left_val, right_val) {
            Ok(Self { left, sep, right })
        } else {
            Err(Error::new_spanned(left, "invalid field specification"))
        }
    }
}

impl ToTokens for FieldPartsLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.left.span();
        let path = MixlibPath::new_spanned(span);
        let left = &self.left;
        let sep = &self.sep;
        let right = &self.right;

        let stream = quote_spanned! {
            span => const {
                #path::num::FieldSpec::from_parts(#left, #right).unwrap()
            }
        };

        tokens.extend(stream);
    }
}

pub struct FieldIntLit {
    lit: LitInt,
}

impl FieldIntLit {
    fn finish_parse(lit: LitInt) -> Result<Self> {
        let val = lit.base10_parse::<i128>()?;
        let left_val = val / 3;
        let right_val = val % 8;

        if field_parts_valid(left_val, right_val) {
            Ok(Self { lit })
        } else {
            Err(Error::new_spanned(lit, "invalid field specification"))
        }
    }
}

impl ToTokens for FieldIntLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let span = self.lit.span();
        let path = MixlibPath::new_spanned(span);
        let lit = &self.lit;

        let stream = quote_spanned! {
            span =>  const {
                #path::num::FieldSpec::from_byte(
                    #path::num::Byte::from_u8(#lit).unwrap()
                ).unwrap()
            }
        };

        tokens.extend(stream);
    }
}

pub enum FieldLit {
    Parts(FieldPartsLit),
    Int(FieldIntLit),
}

impl Parse for FieldLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let NoSuffixInt { lit } = input.parse()?;

        if input.peek(Token![:]) {
            Ok(Self::Parts(FieldPartsLit::finish_parse(input, lit)?))
        } else {
            Ok(Self::Int(FieldIntLit::finish_parse(lit)?))
        }
    }
}

impl ToTokens for FieldLit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            FieldLit::Parts(parts) => parts.to_tokens(tokens),
            FieldLit::Int(int) => int.to_tokens(tokens),
        }
    }
}
