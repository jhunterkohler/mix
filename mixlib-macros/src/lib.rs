//! # `mixlib-macros`
//!
//! This crate is internal. See the macros in `mixlib` for more.

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;

mod parse;
mod path;

use parse::{ByteLit, ShortLit, WordLit};

use crate::parse::FieldLit;

#[doc(hidden)]
#[proc_macro]
pub fn __byte(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as ByteLit);

    quote! { #lit }.into()
}

#[doc(hidden)]
#[proc_macro]
pub fn __short(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as ShortLit);

    quote! { #lit }.into()
}

#[doc(hidden)]
#[proc_macro]
pub fn __word(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as WordLit);

    quote! { #lit }.into()
}

#[doc(hidden)]
#[proc_macro]
pub fn __field(input: TokenStream) -> TokenStream {
    let lit = parse_macro_input!(input as FieldLit);

    quote! { #lit }.into()
}
