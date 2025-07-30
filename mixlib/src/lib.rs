//! # mixlib
//!
//! This crate provides utilities for working with Donald Knuth's MIX
//! computer architecture and MIXAL (the MIX assembly language).

pub mod char;
pub mod fmt;
pub mod num;

#[cfg(not(any(target_pointer_width = "32", target_pointer_width = "64")))]
compile_error!("'target_pointer_width' must be '32' or '64'");
