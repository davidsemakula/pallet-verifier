# Architecture

## Introduction
`pallet-verifier` is a tool for detecting [common security vulnerabilities][vulnerabilities] and [insecure patterns] in
[FRAME pallets][FRAME] using [static program analysis][static-analysis] techniques like [data-flow analysis][data-flow],
[abstract interpretation][abs-int] and [symbolic execution][symbex].

[FRAME pallets][FRAME] are modules used to build/compose [Substrate]-based blockchains.

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
`pallet-verifier` analyzes is Rust's [MIR (Mid-level Intermediate Representation)][MIR]. This is because MIR is
["a radically simplified form of Rust that is [ideal] for certain flow-sensitive [analysis]"][MIR]
(see also [this][MIR-simple] and [this][MIRAI-MIR]).

[Rust]: https://www.rust-lang.org/
[DSL]: https://doc.rust-lang.org/rust-by-example/macros/dsl.html
[MIR]: https://rustc-dev-guide.rust-lang.org/mir/
[MIR-simple]: https://blog.rust-lang.org/2016/04/19/MIR.html#reducing-rust-to-a-simple-core
[MIRAI-MIR]: https://github.com/endorlabs/MIRAI/blob/main/documentation/WhyMir.md

At the highest level, `pallet-verifier` is a custom [Rust compiler (rustc) driver][rustc-driver] which uses
[MIRAI] as a backend for [abstract interpretation][MIRAI-abs-int] (and in the future, also as a
[tag and taint analysis][MIRAI-tag] engine).

Additionally, for a seamless and familiar developer experience, `pallet-verifier` is distributed as a 
[custom cargo sub-command][cargo-sub-cmd] (i.e. `cargo verify-pallet`).

[rustc-driver]: https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html
[MIRAI]: https://github.com/endorlabs/MIRAI
[MIRAI-abs-int]: https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#abstract-interpretation
[MIRAI-tag]: https://github.com/endorlabs/MIRAI/blob/main/documentation/TagAnalysis.md
[cargo-sub-cmd]: https://doc.rust-lang.org/cargo/reference/external-tools.html#custom-subcommands

## Current Capabilities

Currently, `pallet-verifier` focuses on detecting [panics] and [arithmetic overflow/underflow]
(including [overflow checks for narrowing and/or lossy integer cast/`as` conversions that aren't checked by the default Rust compiler][overflow-rfc-updates] - see also [this][overflow-rfc-remove-as] and [this][as-conversions-lossy]) in [dispatchable functions/extrinsics][call] and
public associated functions of [inherent implementations][inherent-impls] of [FRAME pallets][FRAME].
However, other classes of security vulnerabilities (e.g. [insufficient or missing origin checks][origin-checks],
[bad randomness][randomness], [insufficient unsigned transaction validation][validate-unsigned] e.t.c)
will also be targeted in the future.

[panics]: https://secure-contracts.com/not-so-smart-contracts/substrate/dont_panic/
[arithmetic overflow/underflow]: https://secure-contracts.com/not-so-smart-contracts/substrate/arithmetic_overflow/
[overflow-rfc-updates]: https://rust-lang.github.io/rfcs/0560-integer-overflow.html#updates-since-being-accepted
[overflow-rfc-remove-as]: https://github.com/rust-lang/rfcs/pull/1019#issuecomment-88277675
[as-conversions-lossy]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#semantics
[call]: https://docs.rs/frame-support/latest/frame_support/pallet_macros/attr.call.html
[inherent-impls]: https://doc.rust-lang.org/reference/items/implementations.html#inherent-implementations
[origin-checks]: https://secure-contracts.com/not-so-smart-contracts/substrate/origins/
[randomness]: https://secure-contracts.com/not-so-smart-contracts/substrate/randomness/
[validate-unsigned]: https://secure-contracts.com/not-so-smart-contracts/substrate/validate_unsigned/

Additionally, unlike [linting tools][lint] which simply detect problematic [syntactic][syntax] patterns
(e.g. [clippy], [dylint] e.t.c), `pallet-verifier` (using [MIRAI]) goes beyond this by performing a
[flow, path and context-sentitive][analysis-sensitivity] analysis (see also [this][MIRAI-use] and [this][MIRAI-abs-int])
which evaluates the [reachability] of problematic code paths/program states before issuing warnings.
As a concrete example, `pallet-verifier` will not issue a warning for the following code block,
because the branch condition precludes an arithmetic overflow.

```rust
fn bounded_increment(x: u8, bound: u8) -> u8 {
  if x < bound {
    x + 1 // this cannot overflow because `bound <= u8::MAX`
  } else {
    bound
  }
}
```

[lint]: https://en.wikipedia.org/wiki/Lint_(software)
[clippy]: https://github.com/rust-lang/rust-clippy
[dylint]: https://github.com/trailofbits/dylint
[syntax]: https://en.wikipedia.org/wiki/Syntax_(programming_languages)
[analysis-sensitivity]: https://en.wikipedia.org/wiki/Data-flow_analysis#Sensitivities
[MIRAI-use]: https://github.com/endorlabs/MIRAI/blob/main/README.md#who-should-use-mirai
[reachability]: https://en.wikipedia.org/wiki/Reachability_analysis

Lastly, `pallet-verifier` assumes a 32 bit [target pointer width][rustc-target-pointer-width] by default
(i.e. the same pointer width as the `wasm32` and `riscv32` targets), however, this can be overridden using
the `--pointer-width` argument which accepts a value of either `32` or `64` (e.g. `cargo verify-pallet --pointer-width 64`).
The target pointer width is especially relevant for [integer cast/`as` conversions][as-conversions] involving
pointer-sized integer types (i.e. `usize` and `isize`). As a concrete example, the integer cast operation below is
safe in 32 bit execution environments but can overflow in 64 bit execution environments

```rust
fn convert(val: usize) -> u32 {
    val as u32
}
```

**NOTE:** the 64 bit target pointer width option is currently only supported on 64 bit host machines.

[rustc-target-pointer-width]: https://doc.rust-lang.org/reference/conditional-compilation.html#target_pointer_width
[as-conversions]: https://doc.rust-lang.org/reference/expressions/operator-expr.html#type-cast-expressions

## Implementation Details

`pallet-verifier` consists of two binaries:
- A [custom cargo subcommand][cargo-sub-cmd-src] which is the main user-facing component and is invoked via
  `cargo verify-pallet`. It's relatively straightforward, it mostly compiles dependencies using
  appropriate options and compiler flags, before invoking the [custom rustc driver][rustc-driver-src]
  on the target crate (i.e. the [FRAME] pallet).
- A [custom rustc driver][rustc-driver-src] which implements the core functionality of `pallet-verifier`.
  It's typically invoked by the cargo subcommand.

[cargo-sub-cmd-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/main.rs
[rustc-driver-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/driver.rs

The [custom rustc driver][rustc-driver-src] operates in two conceptual phases:
- An [entry point][MIRAI-entrypoint] generation and invariant [annotation][annotations] phase.
- A verification/[abstract interpretation][abs-int] phase.

[MIRAI-entrypoint]: https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#entry-points
[annotations]: https://crates.io/crates/mirai-annotations

### Entry point generation

[Entry point][MIRAI-entrypoint] generation is implemented via a [custom rustc driver callback][enrty-point-callback-src].

[enrty-point-callback-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/callbacks/entry_points.rs

Automatic "tractable" entry point generation is necessary because [FRAME] is inherently a [generic] framework, 
as it makes extensive use of [Rust generic types and traits][rust-generics], however, when performing 
verification/abstract interpretation with [MIRAI], 
["it is not possible for a generic or higher order function to serve as an entry point"][MIRAI-entrypoint], because 
["it is necessary for MIRAI to resolve and analyze all functions that can be reached from an entry point"][MIRAI-entrypoint]
(see also [this][monomorphization] and [this][lowering-MIR]).
So `pallet-verifier` automatically generates "tractable" entry points as singular direct calls to 
[dispatchable functions/extrinsics][call] (and public associated functions of [inherent implementations][inherent-impls]) 
using concrete types from unit tests as substitutions for generic types, while keeping the call arguments 
["abstract"][MIRAI-abstract-value] (in contrast to unit tests, which use 
["concrete"][MIRAI-abstract-value] call arguments, and may also exercise a single target function multiple times, 
leading to under-approximation of program semantics and/or inefficient use of resources during abstract interpretation).

[generic]: https://en.wikipedia.org/wiki/Generic_programming
[rust-generics]: https://doc.rust-lang.org/book/ch10-00-generics.html
[monomorphization]: https://rustc-dev-guide.rust-lang.org/backend/monomorph.html
[lowering-MIR]: https://rustc-dev-guide.rust-lang.org/backend/lowering-mir.html
[MIRAI-abstract-value]: https://github.com/endorlabs/MIRAI/blob/main/documentation/Overview.md#abstract-values

### Invariant annotations

Annotations are implemented/added by overriding the [`optimized-mir` query][optimized-mir-query] using a 
[custom provider][MIR-provider-src] that adds [custom MIR passes][MIR-pass]
(e.g. [a pass that finds all integer `as` conversions that are either narrowing or lossy, and adds overflow checks to them][int-cast-overflow-src]).

[optimized-mir-query]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.optimized_mir
[MIR-pass]: https://rustc-dev-guide.rust-lang.org/mir/passes.html
[MIR-provider-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/providers.rs
[int-cast-overflow-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/providers/int_cast_overflow.rs

[Annotations][annotations] are necessary for either adding checks that aren't included by the default Rust compiler 
(e.g. [overflow checks for narrowing and/or lossy integer cast/`as` conversions][overflow-rfc-updates] - see also 
[this][overflow-rfc-remove-as] and [this][as-conversions-lossy]), or [declaring invariants][annotations] 
that can't be inferred from source code alone, to improve the accuracy of the verifier and reduce false positives 
(e.g. [iterator invariant annotations][iterator-annotations-src]).

[iterator-annotations-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/providers/iterator_annotations.rs

**NOTE:** [Annotations][annotations] require the [mirai-annotations crate][annotations] to be a dependency of the target
[FRAME] pallet that `pallet-verifier` is invoked on, however, it's improbable that this will be the case in the wild, 
so `pallet-verifier` [detects when the `mirai-annotations` crate dependency is missing][annotations-detect-src],
[automatically compiles it][annotations-compile-src] ([see also][annotations-compile-trigger-src]) 
and ["non-invasively" adds it as a dependency][annotations-add-src] (i.e. without modifying the "actual" source code 
and/or `Cargo.toml` manifest of the target [FRAME] pallet).

[annotations-detect-src]: https://github.com/davidsemakula/pallet-verifier/blob/844a49f85f434442202f724c2b5a8aecd0cf9d84/src/cli_utils.rs#L128-L138
[annotations-compile-src]: https://github.com/davidsemakula/pallet-verifier/blob/844a49f85f434442202f724c2b5a8aecd0cf9d84/src/driver.rs#L196-L254
[annotations-compile-trigger-src]: https://github.com/davidsemakula/pallet-verifier/blob/844a49f85f434442202f724c2b5a8aecd0cf9d84/src/main.rs#L180-L223
[annotations-add-src]: https://github.com/davidsemakula/pallet-verifier/blob/844a49f85f434442202f724c2b5a8aecd0cf9d84/src/main.rs#L259-L273

### Verification / Abstract Interpretation

After entry point generation, the "tractable" entry points are passed to [MIRAI] for verification/ abstract interpretation.
This is implemented by [another custom rustc driver callback][verifier-callback-src] that uses [MIRAI] as a library, 
and [determines which diagnostics to either "suppress" or "emit"][diagnostics-filter-src] 
based on our domain-specific knowledge.

[verifier-callback-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/callbacks/verifier.rs
[diagnostics-filter-src]: https://github.com/davidsemakula/pallet-verifier/blob/9051f6200d85b5b5359a12d7da68163fa83090b1/src/callbacks/verifier.rs#L321-L549

**NOTE:** `pallet-verifier` leverages a custom [FileLoader][rust-file-loader] (see [implementation][virtual-file-loader-src]) 
to "virtually" add "analysis-only" external crate declarations and module definitions 
(e.g. `extern crate` declarations for the [mirai-annotations crate][annotations], and module definitions for generated "tractable" entry points and [additional summaries/foreign contracts][contracts-src]) 
to the target [FRAME] pallet without modifying its "actual" source code. 
The ["virtual" FileLoader][virtual-file-loader-src] strategically adds our "analysis-only" external crate declarations 
and module definitions in a way that leverages `rustc`'s excellent support for [incremental compilation/analysis][rustc-inc-comp-detail] 
(see also [this][rustc-inc-comp] and [this][rustc-query]), meaning unrelated code is never recompiled during the verification/abstract intepretation phase.

[rust-file-loader]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/source_map/trait.FileLoader.html
[virtual-file-loader-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/src/file_loader.rs
[contracts-src]: https://github.com/davidsemakula/pallet-verifier/blob/master/artifacts/contracts.rs
[rustc-inc-comp-detail]: https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation-in-detail.html
[rustc-inc-comp]: https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html
[rustc-query]: https://rustc-dev-guide.rust-lang.org/query.html


