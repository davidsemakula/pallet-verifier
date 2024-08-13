# Pallet Verifier

pallet-verifier is a tool for detecting [common security vulnerabilities][vulnerabilities] and [insecure patterns] in
[FRAME pallets][FRAME] using [static program analysis][static-analysis] techniques like [data-flow analysis][data-flow],
[abstract interpretation][abs-int] and [symbolic execution][symbex].

[FRAME pallets][FRAME] are modules that are used to build/compose [Substrate]-based blockchains.

[FRAME]: https://docs.substrate.io/learn/runtime-development/#frame
[Substrate]: https://docs.substrate.io/
[vulnerabilities]: https://secure-contracts.com/not-so-smart-contracts/substrate/
[insecure patterns]: https://docs.substrate.io/build/troubleshoot-your-code/#unsafe-or-insecure-patterns
[static-analysis]: https://en.wikipedia.org/wiki/Static_program_analysis
[data-flow]: https://en.wikipedia.org/wiki/Data-flow_analysis
[abs-int]: https://en.wikipedia.org/wiki/Abstract_interpretation
[symbex]: https://en.wikipedia.org/wiki/Symbolic_execution

**NOTE:** 🚧 This project is still work in progress, check back over the next few weeks for regular updates.

## Installation

### Prerequisites

- [Rust, rustup and cargo](https://doc.rust-lang.org/book/ch01-01-installation.html)
- [Clang](https://clang.llvm.org/get_started.html)
- [Cmake](https://cmake.org/download/)

### Installing `pallet-verifier`

```shell
git clone https://github.com/davidsemakula/pallet-verifier.git
cd pallet-verifier
cargo install --locked --path ./
```

## Usage

Run the following command from the crate root of a FRAME pallet
(i.e. the directory that contains the `Cargo.toml` file for the FRAME pallet).

```shell
cargo verify-pallet
```

**NOTE:** `pallet-verifier` compiles the target FRAME pallet code in "test mode" (i.e. the equivalent of running 
`cargo test` or `rustc --test`), so you'll need to ensure that all prerequisites for test compilation 
are installed and/or configured properly, otherwise compilation will fail.

## License

Licensed under either [MIT](/LICENSE-MIT) or [Apache-2.0](/LICENSE-APACHE) license at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
