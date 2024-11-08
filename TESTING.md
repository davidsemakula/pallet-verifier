# Pallet Verifier: Testing Guide

## Setup

Follow the installation instructions outlined in the project [README.md][README-install]

[README-install]: /README.md#installation

## Running UI tests

You can run [UI tests][rustc-ui-tests] by running the following command from the project root:

```shell
cargo test
```

[rustc-ui-tests]: https://rustc-dev-guide.rust-lang.org/tests/ui.html

## Test Structure

Like the [Rust compiler][rustc] itself, `pallet-verifier` is mainly tested using [UI tests][rustc-ui-tests] 
(i.e. ["a collection of general-purpose tests which primarily focus on validating the console output of the compiler"][rustc-ui-tests-intro]).
And similar to other Rust compiler plugins (like [clippy] and [miri]), `pallet-verifier` also leverages 
the [ui_test framework][ui_test-crate] as its [UI tests runner][ui-tests-runner].

[rustc]: https://github.com/rust-lang/rust
[rustc-ui-tests-intro]: https://rustc-dev-guide.rust-lang.org/tests/ui.html#introduction
[clippy]: https://github.com/rust-lang/rust-clippy
[miri]: https://github.com/rust-lang/miri
[ui_test-crate]: https://crates.io/crates/ui_test
[ui-tests-runner]: https://github.com/davidsemakula/pallet-verifier/blob/master/tests/compile-test.rs
[ui-tests-src]: https://github.com/davidsemakula/pallet-verifier/tree/master/tests/ui

`pallet-verifier`'s [UI tests][ui-tests-src] are defined in the [tests/ui][ui-tests-src] directory.
Test cases are divided into three main test suites, each in its own subdirectory: 
- [tests/ui/driver][ui-tests-src-driver]: for testing minimal direct calls to the [custom rustc driver][rustc-driver-src] (i.e. without [cargo]).
- [tests/ui/cargo][ui-tests-src-cargo]: for testing calls via the [custom cargo subcommand][cargo-sub-cmd-src] (i.e. `cargo verify-pallet`).
- [tests/ui/sdk][ui-tests-src-sdk]: for testing a few production [FRAME] pallets from the [Polkadot SDK][polkadot-sdk].

[ui-tests-src-driver]: https://github.com/davidsemakula/pallet-verifier/tree/master/tests/ui/driver
[rustc-driver-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/driver.rs
[cargo]: https://doc.rust-lang.org/cargo/
[ui-tests-src-cargo]: https://github.com/davidsemakula/pallet-verifier/tree/master/tests/ui/cargo
[cargo-sub-cmd-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/main.rs
[ui-tests-src-sdk]: https://github.com/davidsemakula/pallet-verifier/tree/master/tests/ui/sdk
[FRAME]: https://docs.substrate.io/learn/runtime-development/#frame
[polkadot-sdk]: https://github.com/paritytech/polkadot-sdk

However, at a higher-level, test cases in the [tests/ui/driver][ui-tests-src-driver] and [tests/ui/cargo][ui-tests-src-cargo] 
test suites are essentially minimal sanity checks with descriptive names based on the specific feature/behaviour 
they check/validate (e.g. [this][ui-test-driver-int-cast-overflow] and [this][ui-test-cargo-int-cast-overflow] 
for [integer cast overflow detection][arch-caps]), while test cases in the [tests/ui/sdk][ui-tests-src-sdk] test suite 
are production [FRAME] pallet tests, and include FRAME pallets copied directly from the [Polkadot SDK][polkadot-sdk].

[ui-test-driver-int-cast-overflow]: https://github.com/davidsemakula/pallet-verifier/blob/master/tests/ui/driver/tractable-skeleton-int-cast-overflow.rs
[ui-test-cargo-int-cast-overflow]: https://github.com/davidsemakula/pallet-verifier/tree/master/tests/ui/cargo/minimal-tractable-int-cast-overflow
[arch-caps]: /ARCHITECTURE.md#current-capabilities

The expected `stdout` and `stderr` output for each test case is defined in `*.stdout` and `*.stderr` files 
(e.g. see [this][pallet-multisig-stdout] and [this][pallet-multisig-stderr], or [this][driver-int-cast-overflow-stdout] 
and [this][driver-int-cast-overflow-stderr]), with the absence of a `*.stderr` file implying that a test case has 
no expected diagnostics.

[pallet-multisig-stdout]: https://github.com/davidsemakula/pallet-verifier/blob/master/tests/ui/sdk/multisig/Cargo.stdout
[pallet-multisig-stderr]: https://github.com/davidsemakula/pallet-verifier/blob/master/tests/ui/sdk/multisig/Cargo.stderr
[driver-int-cast-overflow-stdout]: https://github.com/davidsemakula/pallet-verifier/blob/master/tests/ui/driver/tractable-skeleton-int-cast-overflow.stdout
[driver-int-cast-overflow-stderr]: https://github.com/davidsemakula/pallet-verifier/blob/master/tests/ui/driver/tractable-skeleton-int-cast-overflow.stderr
