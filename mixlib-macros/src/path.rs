//! Library utilities.

use proc_macro_crate::{FoundCrate, crate_name};
use proc_macro2::{Ident, Span, TokenStream};
use quote::{ToTokens, quote_spanned};

pub struct MixlibPath {
    stream: TokenStream,
}

impl MixlibPath {
    pub fn new_spanned(span: Span) -> Self {
        let found = crate_name("mixlib")
            .expect("`mixlib` should be present in Cargo.toml");

        let name = match &found {
            FoundCrate::Itself => "mixlib",
            FoundCrate::Name(name) => name,
        };

        let ident = Ident::new(name, span);
        let stream = quote_spanned! { span => ::#ident };

        Self { stream }
    }
}

impl ToTokens for MixlibPath {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.stream.to_tokens(tokens);
    }
}
