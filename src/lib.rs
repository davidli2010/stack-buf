//! Vector-like facade for arrays allocated entirely on the stack.
//!
//! Shallow wrapper around an underlying `[T; N]`, which panics if the
//! array bounds are exceeded.
//!
//! ## Optional features
//!
//! ### `serde`
//!
//! When this optional dependency is enabled, `StackVec` implements the `serde::Serialize` and
//! `serde::Deserialize` traits.
//!
//! ## Rust Version
//!
//! This version of `stack-buf` requires Rust 1.51 or later.

mod vec;

pub use vec::{Drain, IntoIter, StackVec};
