# SPDX-License-Identifier: Apache-2.0

cargo build
cargo build --features std
cargo build --target thumbv6m-none-eabi
cargo test
cargo test --no-default-features
cargo test --no-default-features --features heapless
cargo test --no-default-features --features std
cargo test --no-default-features --features heapless,std
cargo doc
