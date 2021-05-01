//! Vector-like facade for arrays allocated entirely on the stack.
//!
//! Shallow wrapper around an underlying `[T; N]`, which panics if the
//! array bounds are exceeded.
//!
//! ## Optional features
//!
//! ### `str`
//!
//! When this optional dependency is enabled, `StackStr` is available.
//!
//! ### `serde`
//!
//! When this optional dependency is enabled, `StackVec` and `StackStr` implement the `serde::Serialize` and
//! `serde::Deserialize` traits.
//!
//! ## Rust Version
//!
//! This version of `stack-buf` requires Rust 1.51 or later.

mod vec;

pub use crate::vec::{Drain, IntoIter, StackVec};

#[cfg(feature = "str")]
mod str;

#[cfg(feature = "str")]
pub use crate::str::{FromUtf8Error, StackStr};
