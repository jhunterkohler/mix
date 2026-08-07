use proc_macro2::TokenStream;
use quote::{ToTokens, quote, quote_spanned};
use syn::{
    Error, Ident, LitInt, Path, Result, Token,
    parse::{Parse, ParseStream},
    parse_quote,
    punctuated::{Pair, Punctuated},
    spanned::Spanned,
};

trait ToTokensWithPath {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream);

    fn to_token_stream_with_path(&self, path: &Path) -> TokenStream {
        let mut tokens = TokenStream::new();
        self.to_tokens_with_path(path, &mut tokens);
        tokens
    }
}

pub enum SignLit {
    Plus(Token![+]),
    Minus(Token![-]),
}

impl ToTokensWithPath for SignLit {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        match self {
            SignLit::Plus(plus) => {
                quote_spanned! { plus.span() => #path::num::Sign::Plus }
                    .to_tokens(tokens);
            }
            SignLit::Minus(minus) => {
                quote_spanned! { minus.span() => #path::num::Sign::Minus }
                    .to_tokens(tokens);
            }
        };
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

const BYTE_MAX: i128 = 63;
const BYTE_MIN: i128 = 0;
const SHORT_MAX: i128 = (1 << 12) - 1;
const SHORT_MIN: i128 = -SHORT_MAX;
const WORD_MAX: i128 = (1 << 30) - 1;
const WORD_MIN: i128 = -WORD_MAX;

fn parse_int_in_range(
    input: ParseStream,
    name: &str,
    min: i128,
    max: i128,
) -> Result<(LitInt, i128)> {
    let lit: LitInt = input.parse()?;
    let value: i128 = lit.base10_parse()?;

    if value >= min && value <= max {
        Ok((lit, value))
    } else {
        let msg = format!(
            "literal value '{value}' out of range of {name} ({min}..={max})"
        );

        Err(Error::new(lit.span(), msg))
    }
}

pub struct ByteLit {
    value: u8,
    lit: LitInt,
}

impl ToTokensWithPath for ByteLit {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        let value = self.value;

        quote_spanned! {
            self.lit.span() =>
                const { #path::num::Byte::from_u8(#value).unwrap() }
        }
        .to_tokens(tokens);
    }
}

impl Parse for ByteLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let (lit, value) =
            parse_int_in_range(input, "MIX byte", BYTE_MIN, BYTE_MAX)?;

        Ok(Self { value: value as u8, lit })
    }
}

pub struct BytesList<const N: usize> {
    parts: Punctuated<ByteLit, Token![,]>,
}

impl<const N: usize> ToTokensWithPath for BytesList<N> {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        let mut inner = TokenStream::new();

        for elem in self.parts.pairs() {
            match elem {
                Pair::Punctuated(byte_lit, comma) => {
                    byte_lit.to_tokens_with_path(path, &mut inner);
                    comma.to_tokens(&mut inner);
                }
                Pair::End(byte_lit) => {
                    byte_lit.to_tokens_with_path(path, &mut inner);
                }
            }
        }

        quote! { [#inner] }.to_tokens(tokens)
    }
}

impl<const N: usize> Parse for BytesList<N> {
    fn parse(input: ParseStream) -> Result<Self> {
        let parts = Punctuated::parse_terminated(input)?;

        if parts.len() == N {
            Ok(Self { parts })
        } else {
            Err(input.error(format!("expected {N} bytes")))
        }
    }
}

pub struct SignedBytesList<const N: usize> {
    sign: SignLit,
    sep: Token![,],
    parts: BytesList<N>,
}

impl<const N: usize> ToTokensWithPath for SignedBytesList<N> {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        self.sign.to_tokens_with_path(path, tokens);
        self.sep.to_tokens(tokens);
        self.parts.to_tokens_with_path(path, tokens);
    }
}

impl<const N: usize> Parse for SignedBytesList<N> {
    fn parse(input: ParseStream) -> Result<Self> {
        let sign = input.parse()?;
        let sep = input.parse()?;
        let parts = input.parse()?;

        Ok(Self { sign, sep, parts })
    }
}

pub type ShortBytesLit = SignedBytesList<2>;
pub type WordBytesLit = SignedBytesList<5>;

fn default_sign_to_tokens(path: &Path, tokens: &mut TokenStream) {
    quote! { #path::num::Sign::Plus }.to_tokens(tokens)
}

pub struct ShortIntLit {
    sign: Option<SignLit>,
    value: u16,
    lit: LitInt,
}

impl ToTokensWithPath for ShortIntLit {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        if let Some(sign) = &self.sign {
            sign.to_tokens_with_path(path, tokens);
        } else {
            default_sign_to_tokens(path, tokens);
        }

        let value = self.value;

        quote! { , }.to_tokens(tokens);
        quote_spanned! { self.lit.span() => #value }.to_tokens(tokens);
    }
}

impl Parse for ShortIntLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let sign = if input.peek(Token![-]) || input.peek(Token![+]) {
            Some(input.parse()?)
        } else {
            None
        };

        let (lit, value) =
            parse_int_in_range(input, "MIX short", SHORT_MIN, SHORT_MAX)?;

        Ok(Self { sign, value: value as u16, lit })
    }
}

pub struct WordIntLit {
    sign: Option<SignLit>,
    value: u32,
    lit: LitInt,
}

impl ToTokensWithPath for WordIntLit {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        if let Some(sign) = &self.sign {
            sign.to_tokens_with_path(path, tokens);
        } else {
            default_sign_to_tokens(path, tokens);
        }

        let value = self.value;
        quote! { , }.to_tokens(tokens);
        quote_spanned! { self.lit.span() => #value }.to_tokens(tokens);
    }
}

impl Parse for WordIntLit {
    fn parse(input: ParseStream) -> Result<Self> {
        let sign = if input.peek(Token![-]) || input.peek(Token![+]) {
            Some(input.parse()?)
        } else {
            None
        };

        let (lit, value) =
            parse_int_in_range(input, "MIX word", WORD_MIN, WORD_MAX)?;

        Ok(Self { sign, value: value as u32, lit })
    }
}

pub enum ShortLit {
    Bytes(ShortBytesLit),
    Int(ShortIntLit),
}

impl ToTokensWithPath for ShortLit {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        match self {
            ShortLit::Bytes(byte_list) => {
                let byte_list = byte_list.to_token_stream_with_path(path);
                quote! {
                    const { #path::num::Short::from_sign_bytes(#byte_list) }
                }
                .to_tokens(tokens)
            }
            ShortLit::Int(inner) => {
                let inner = inner.to_token_stream_with_path(path);
                quote! {
                    const { #path::num::Short::from_sign_u16(#inner).unwrap() }
                }
                .to_tokens(tokens)
            }
        };
    }
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

pub enum WordLit {
    Bytes(WordBytesLit),
    Int(WordIntLit),
}

impl ToTokensWithPath for WordLit {
    fn to_tokens_with_path(&self, path: &Path, tokens: &mut TokenStream) {
        match self {
            WordLit::Bytes(byte_list) => {
                let byte_list = byte_list.to_token_stream_with_path(path);
                quote! {
                    const { #path::num::Word::from_sign_bytes(#byte_list) }
                }
                .to_tokens(tokens)
            }
            WordLit::Int(inner) => {
                let inner = inner.to_token_stream_with_path(path);
                quote! {
                    const { #path::num::Word::from_sign_u32(#inner).unwrap() }
                }
                .to_tokens(tokens)
            }
        };
    }
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

pub struct WithPath<T> {
    path: Path,
    inner: T,
}

impl<T: ToTokensWithPath> ToTokens for WithPath<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.inner.to_tokens_with_path(&self.path, tokens);
    }
}

impl<T: Parse> Parse for WithPath<T> {
    fn parse(input: ParseStream) -> Result<Self> {
        let path = if input.peek(Ident) {
            let path = input.parse()?;
            input.parse::<Token![,]>()?;
            path
        } else {
            parse_quote! { ::mixlib }
        };

        let inner = input.parse()?;

        Ok(Self { path, inner })
    }
}
