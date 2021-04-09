//! Vector-like facade for arrays allocated entirely on the stack.
//!
//! Shallow wrapper around an underlying `[T; N]`, which panics if the
//! array bounds are exceeded.
//!
//! ## Rust Version
//!
//! This version of `stack-buf` requires Rust 1.51 or later.

mod vec;

pub use vec::StackVec;
