# Pallet Verifier

## Introduction
`pallet-verifier` is a tool for detecting [common security vulnerabilities][vulnerabilities] and [insecure patterns] in
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

## High-Level Design

[FRAME] is a [Rust]-based [DSL (Domain Specific Language)][DSL], therefore, the source code representation that
pallet-verifier analyzes is Rust's [MIR (Mid-level Intermediate Representation)][MIR]. This is because MIR is
["a radically simplified form of Rust that is [ideal] for certain flow-sensitive [analysis]"][MIR]
(see also [this][MIR-simple] and [this][MIRAI-MIR]).

[Rust]: https://www.rust-lang.org/
[DSL]: https://doc.rust-lang.org/rust-by-example/macros/dsl.html
[MIR]: https://rustc-dev-guide.rust-lang.org/mir/
[MIR-simple]: https://blog.rust-lang.org/2016/04/19/MIR.html#reducing-rust-to-a-simple-core
[MIRAI-MIR]: https://github.com/endorlabs/MIRAI/blob/main/documentation/WhyMir.md

At the highest level, `pallet-verifier` is a custom [rust compiler (rustc) driver][rustc-driver] which uses
[MIRAI] as a backend for [abstract interpretation][MIRAI-abs-int] (and in the future, also as a
[tag and taint analysis][MIRAI-tag] engine).

Additionally, for a seamless and familiar developer experience, `pallet-verifier` is distributed as a 
[custom cargo sub-command][cargo-sub-cmd] (`cargo verify-pallet`).

[rustc-driver]: https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html
[MIRAI]: https://github.com/endorlabs/MIRAI
[MIRAI-abs-int]: https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#abstract-interpretation
[MIRAI-tag]: https://github.com/endorlabs/MIRAI/blob/main/documentation/TagAnalysis.md
[cargo-sub-cmd]: https://doc.rust-lang.org/cargo/reference/external-tools.html#custom-subcommands

## Implementation Details

`pallet-verifier` consists of two binaries:
- a [custom cargo subcommand][cargo-sub-cmd-src] which is the main user 
  facing component and is invoked via `cargo verify-pallet`.
- a [custom rustc driver][rustc-driver-src] which is invoked by the cargo subcommand.

[cargo-sub-cmd-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/main.rs
[rustc-driver-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/driver.rs

The [custom cargo subcommand][cargo-sub-cmd-src] is relatively minimal and mostly compiles dependencies using 
appropriate options and compiler flags, before invoking the [custom rustc driver][rustc-driver-src] on the target crate 
(i.e. the [FRAME] pallet).

The [custom rustc driver][rustc-driver-src] implements the core functionality of `pallet-verifier`. 
It operates in two conceptual phases:
- First an analysis, annotation and entry-point generation phase.
- Then finally a verification/ abstract interpretation phase.

### Analysis, annotation and entry-point generation

Entry-point generation is implemented via a [custom rustc driver callback][enrty-point-callback-src], 
while annotations (and assertions) are implemented/added by overriding the [`optimized-mir` query][optimized-mir-query] 
using a [custom provider][MIR-provider-src] that adds [custom MIR passes][MIR-pass] 
(e.g. [a pass that finds all integer `as` conversions that are either narrowing or lossy conversions and adds for overflow checks][int-cast-overflow-src]).

[enrty-point-callback-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/callbacks/entry_points.rs
[optimized-mir-query]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.optimized_mir
[MIR-pass]: https://rustc-dev-guide.rust-lang.org/mir/passes.html
[MIR-provider-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/providers.rs
[int-cast-overflow-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/providers/int_cast_overflow.rs

Automatic entry point generation is necessary because [FRAME] is inherently a [generic] framework as it makes extensive use of
[Rust generic types and traits][rust-generics], while, when performing verification/abstract interpretation with MIRAI, 
["it is not possible for a generic or higher order function to serve as an entry point"][MIRAI-entrypoint]. 
This is because ["it is necessary for MIRAI to resolve and analyze all functions that can be reached from an entry point"][MIRAI-entrypoint].

Annotations (and additional assertions) are necessary to either add checks that aren't included by the default rust compiler 
(e.g. [overflow checks for narrowing and/or lossy integer cast conversions][overflow-rfc-design] ([see also][overflow-rfc-remove-as])),
or [declare invariants that can't be inferred from source code alone to improve the accuracy of the verifier and reduce false positives][MIRAI-annotations] 
(e.g. [iterator related annotations][iterator-annotations-src]).

[MIRAI-entrypoint]: https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#entry-points
[generic]: https://en.wikipedia.org/wiki/Generic_programming
[rust-generics]: https://doc.rust-lang.org/book/ch10-00-generics.html
[overflow-rfc-design]: https://rust-lang.github.io/rfcs/0560-integer-overflow.html#detailed-design
[overflow-rfc-remove-as]: https://github.com/rust-lang/rfcs/pull/1019#issuecomment-88277675
[MIRAI-annotations]: https://crates.io/crates/mirai-annotations
[iterator-annotations-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/providers/iterator_annotations.rs

### Verification / Abstract Interpretation

After entry-point generation, the generated entry points are passed to [MIRAI] for verification/ abstract interpretation.
This is implemented by [another custom rustc driver callback][verifier-callback-src] that 
essentially uses [MIRAI] as library.

[verifier-callback-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/callbacks/verifier.rs

## Current Capabilities

Currently, `pallet-verifier` focuses on detecting [panics] and [arithmetic overflow/underflow]
(and [lossy integer conversions][as-conversions-lossy]) in [dispatchable functions/extrinsics][call] of [FRAME pallets][FRAME].
However, the goal is also target other classes of security vulnerabilities (e.g. [insufficient or missing origin checks][origin-checks],
[bad randomness][randomness], [insufficient unsigned transaction validation][validate-unsigned] e.t.c) in the future.

[panics]: https://secure-contracts.com/not-so-smart-contracts/substrate/dont_panic/
[arithmetic overflow/underflow]: https://secure-contracts.com/not-so-smart-contracts/substrate/arithmetic_overflow/
[as-conversions-lossy]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#semantics
[call]: https://docs.rs/frame-support/latest/frame_support/pallet_macros/attr.call.html
[origin-checks]: https://secure-contracts.com/not-so-smart-contracts/substrate/origins/
[randomness]: https://secure-contracts.com/not-so-smart-contracts/substrate/randomness/
[validate-unsigned]: https://secure-contracts.com/not-so-smart-contracts/substrate/validate_unsigned/

