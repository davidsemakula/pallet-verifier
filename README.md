# pallet-verifier

`pallet-verifier` is a tool for detecting [common security vulnerabilities][vulnerabilities] and [insecure patterns] in
[FRAME pallets][FRAME] using [static program analysis][static-analysis] techniques like [data-flow analysis][data-flow],
[abstract interpretation][abs-int] and [symbolic execution][symbex].

[FRAME pallets][FRAME] are modules used to build/compose [Substrate]-based blockchains.

- [Introductory blog post][blog-intro].

[FRAME]: https://docs.substrate.io/learn/runtime-development/#frame
[Substrate]: https://docs.substrate.io/
[vulnerabilities]: https://secure-contracts.com/not-so-smart-contracts/substrate/
[insecure patterns]: https://docs.substrate.io/build/troubleshoot-your-code/#unsafe-or-insecure-patterns
[static-analysis]: https://en.wikipedia.org/wiki/Static_program_analysis
[data-flow]: https://en.wikipedia.org/wiki/Data-flow_analysis
[abs-int]: https://en.wikipedia.org/wiki/Abstract_interpretation
[symbex]: https://en.wikipedia.org/wiki/Symbolic_execution
[blog-intro]: https://davidsemakula.com/blog/introducing-pallet-verifier

**NOTE:** 🚧 This project is still work in progress, check back over the next few weeks for regular updates.

## Installation

### Prerequisites

- [Rust, rustup and cargo](https://doc.rust-lang.org/book/ch01-01-installation.html)
- [Clang](https://clang.llvm.org/get_started.html)
- [Cmake](https://cmake.org/download/)

**NOTE:** `pallet-verifier` requires a `Clang` binary that supports [`WebAssembly`](https://webassembly.org/).
On `macOS`, the `Clang` binary from `Xcode` doesn't support `WebAssembly`, so you'll need to install 
[`clang/llvm` via `homebrew`](https://formulae.brew.sh/formula/llvm) and add it to your `PATH`.

**NOTE:** On platforms where [`gcc`](https://gcc.gnu.org/) is the default `C` compiler (e.g. Debian and Ubuntu), 
make sure the [`gcc-multilib`](https://packages.debian.org/sid/gcc-multilib) package is also installed.

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

## Documentation

### Binary Documentation

`cargo verfiy-pallet` subcommand help text.

```console
A tool for detecting common security vulnerabilities and insecure patterns in FRAME pallets using static program analysis techniques.

Usage: cargo verify-pallet

Options:
    -h, --help                   Print help
    -V, --version                Print version
    --pointer-width <32|64>      The pointer width for the target execution environment
    --allow-hook-panics <list>   The hooks in which no warnings should be reported for local panics.
                                     Accepts a comma separated list from: `on_initialize`,`on_finalize`,`on_idle`,`on_poll`,`on_runtime_upgrade`,`offchain_worker`,`integrity_test`
```

### Library Documentation

You can access library documentation locally by running the following command from the project root

```shell
cargo doc --no-deps --open
```

### Architecture Documentation

To learn more about how `pallet-verifier` works under the hood, check out [ARCHITECTURE.md](/ARCHITECTURE.md) ([see also][blog-intro]).

## Testing

You can run [UI tests](https://rustc-dev-guide.rust-lang.org/tests/ui.html) by running the following command from the project root

```shell
cargo test
```

Check out [TESTING.md](/TESTING.md) for more details.

## License

Licensed under either [MIT](/LICENSE-MIT) or [Apache-2.0](/LICENSE-APACHE) license at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

## Acknowledgements

🌱 Funded by: the [Web3 Foundation](https://web3.foundation/).