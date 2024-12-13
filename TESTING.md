# Testing Guide

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

## The custom benchmark

`pallet-verifier` includes a simple [custom benchmark][benchmark-src] used to test its accuracy and speed on 
a few production pallets from the [Polkadot SDK][polkadot-sdk].

[benchmark-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/benches/bencher.rs

You can run the benchmark by running the following command from the project root:

```shell
cargo bench
```

The [benchmark][benchmark-src] works by invoking `pallet-verifier` on 2 versions/variants of 
each production FRAME pallet in the [benchmark suite][benchmark-src-dir]: 
- An "sdk version" copied from the [Polkadot SDK][polkadot-sdk] at [this commit][polkadot-sdk-commit] 
  (e.g. [see this][benchmark-multisig-sdk-dir])
- An "edited version" that either introduces an issue or fixes an issue (e.g. [see this][benchmark-multisig-edit-dir])

It then compares the returned diagnostics, to [fixtures that describe the expected results][benchmark-fixtures] 
([see also][benchmark-fixtures-types]), and reports metrics including:
- the number "expected" and "actual/found" diagnostics
- the number of ["true positives", "false positives", "false negatives"][benchmark-compare-results]
- the total execution time

at different levels of granularity i.e for: 
- each dispatchable or public associated function 
- each pallet version/variant (both "sdk" and "edited")
- the entire benchmark suite

[benchmark-src-dir]: https://github.com/davidsemakula/pallet-verifier/blob/master/benches/
[polkadot-sdk-commit]: https://github.com/paritytech/polkadot-sdk/tree/515fcc952cd52504ab7d3866a83adb9bf0f8e56b
[benchmark-multisig-sdk-dir]: https://github.com/davidsemakula/pallet-verifier/tree/master/benches/multisig/sdk
[benchmark-multisig-edit-dir]: https://github.com/davidsemakula/pallet-verifier/tree/master/benches/multisig/edit
[benchmark-fixtures]: https://github.com/davidsemakula/pallet-verifier/blob/91039a593af0907b2e704fa38c1f0db0138b7ede/benches/bencher.rs#L231-L333
[benchmark-fixtures-types]: https://github.com/davidsemakula/pallet-verifier/blob/91039a593af0907b2e704fa38c1f0db0138b7ede/benches/bencher.rs#L394-L422
[benchmark-compare-results]: https://github.com/davidsemakula/pallet-verifier/blob/91039a593af0907b2e704fa38c1f0db0138b7ede/benches/bencher.rs#L335-L392

Check out the inline comments in the [benchmark runner][benchmark-src] for more details.