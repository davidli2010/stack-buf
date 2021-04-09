//! Vector-like facade for arrays allocated entirely on the stack.
//!
//! Shallow wrapper around an underlying `[T; N]`, which panics if the
//! array bounds are exceeded.
