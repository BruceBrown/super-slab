# SuperSlab

Pre-allocated storage for a uniform data type.

[![Crates.io](https://img.shields.io/crates/v/slab.svg?maxAge=2592000)](https://crates.io/crates/super-slab)
[![Build Status](https://github.com/BruceBrown/super-slab/workflows/Rust/badge.svg)](
https://github.com/brucebrown/super-slab/actions)
[![Test Status](https://github.com/BruceBrown/super-slab/workflows/Tests/badge.svg)](
https://github.com/brucebrown/super-slab/actions)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](
https://github.com/BruceBrown/d3#license)
[![Cargo](https://img.shields.io/crates/v/super-slab.svg)](
https://crates.io/crates/super-slab)
[![Documentation](https://docs.rs/super-slab/badge.svg)](
https://docs.rs/super-slab)
[![Rust 1.47+](https://img.shields.io/badge/rust-1.47+-color.svg)](
https://www.rust-lang.org)

[Documentation](https://docs.rs/super-slab)

## Usage

To use `super-slab`, first add this to your `Cargo.toml`:

```toml
[dependencies]
super-slab = "0.1.0"
```

Next, add this to your crate:

```rust

use super_slab::SuperSlab;

let mut slab = SuperSlab::new();

let hello = slab.insert("hello");
let world = slab.insert("world");

assert_eq!(slab[hello], "hello");
assert_eq!(slab[world], "world");

slab[world] = "earth";
assert_eq!(slab[world], "earth");
```

See [documentation](https://docs.rs/super-slab) for more details.

## License

Licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in `super-slab` by you, shall be shall be dual licensed as above,
without any additional terms or conditions.
