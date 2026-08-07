//! # `mixlib-macros`
//!
//! This crate is internal. See the macros in `mixlib` for more.

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

mod lit;

use lit::{ByteLit, ShortLit, WithPath, WordLit};

#[doc(hidden)]
#[proc_macro]
pub fn __byte(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as WithPath<ByteLit>);

    quote! { #lit }.into()
}

#[doc(hidden)]
#[proc_macro]
pub fn __short(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as WithPath<ShortLit>);

    quote! { #lit }.into()
}

#[doc(hidden)]
#[proc_macro]
pub fn __word(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as WithPath<WordLit>);

    quote! { #lit }.into()
}
