# stack-buf

[![Crates.io: stack-buf](https://img.shields.io/crates/v/stack-buf.svg)](https://crates.io/crates/stack-buf)
[![Documentation](https://docs.rs/stack-buf/badge.svg)](https://docs.rs/stack-buf)

[![License: Apache](https://img.shields.io/badge/License-Apache%202.0-red.svg)](LICENSE-APACHE)
OR
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)

Vector-like facade for arrays allocated entirely on the stack. Shallow wrapper around an underlying `[T; N]`, which panics if the array bounds are exceeded.

Please read the [`API docs here`](https://docs.rs/stack-buf).

## Optional features

### `serde`

When this optional dependency is enabled, `StackVec` implements the `serde::Serialize` and `serde::Deserialize` traits.

## Rust Version

This version of `stack-buf` requires Rust 1.51 or later.

## License

Dual-licensed to be compatible with the Rust project.

Licensed under the Apache License, Version 2.0
http://www.apache.org/licenses/LICENSE-2.0 or the MIT license
http://opensource.org/licenses/MIT, at your
option. This file may not be copied, modified, or distributed
except according to those terms.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `stack-buf` by you, shall be licensed as Apache-2.0 and MIT, without any additional
terms or conditions.

## Acknowledgment

`stack-buf` is inspired by [`arrayvec`](https://github.com/bluss/arrayvec) and [`stackvector`](https://github.com/Alexhuszagh/rust-stackvector), and copy code snippets from them.
