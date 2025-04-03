//! Custom benchmark runner for checking speed and accuracy of `pallet-verifeir` on production pallets.

use std::{
    cmp::Ordering,
    collections::HashMap,
    env,
    path::PathBuf,
    process::Command,
    time::{Duration, Instant},
};

use itertools::Itertools;
use owo_colors::{OwoColorize, Style};

use pallet_verifier::CallKind;

/// The benchmark runner.
/// See [fixtures] for definitions, and [FixtureGroup] and [Fixture] for descriptions.
fn main() {
    // Colorization styles.
    let green_bold = Style::new().green().bold();
    let yellow_bold = Style::new().yellow().bold();
    let green = Style::new().green();
    let red = Style::new().red();

    // Finds benchmark name filter.
    let filter = env::args().skip(1).find(|arg| !arg.starts_with("--"));

    // Runs `pallet-verifier` for described fixtures and analyzes results.
    // See [fixtures] for definitions, and [FixtureGroup] and [Fixture] for descriptions.
    let mut n_passed_total = 0;
    let mut n_failed_total = 0;
    let mut n_filtered_out = 0;
    let mut n_true_positives_total = 0;
    let mut n_false_positives_total = 0;
    let mut n_false_negative_total = 0;
    let mut total_elapsed = Duration::ZERO;
    for fixture_group in fixtures() {
        let FixtureGroup {
            pallet_name,
            sdk: sdk_fixture,
            edit: edit_fixture,
            ..
        } = fixture_group;
        let is_active = filter.is_none()
            || filter
                .as_ref()
                .is_some_and(|filter| fixture_group.pallet_name == filter);
        println!(
            "\n{} pallet-{pallet_name}",
            if is_active {
                "Benching".style(green_bold)
            } else {
                "Skipping".style(yellow_bold)
            }
        );
        if !is_active {
            n_filtered_out += 1;
            continue;
        }

        let bench_path = format!("benches/{pallet_name}");
        for (fixture_kind, fixture) in [
            (FixtureKind::SDK, sdk_fixture),
            (FixtureKind::Edit, edit_fixture),
        ] {
            // Outputs info about pallet variant being analyzed.
            let comment = fixture.comment;
            println!(
                "{}{} {bench_path} ({} version)\n{}{}{}",
                indent_by_level(1),
                "Analyzing".style(green_bold),
                match fixture_kind {
                    FixtureKind::SDK => "sdk",
                    FixtureKind::Edit => "edited",
                },
                if comment.is_empty() {
                    "".to_owned()
                } else {
                    format!("{}Comment: ", indent_by_level(2))
                },
                comment
                    .lines()
                    .enumerate()
                    .map(|(idx, line)| if idx == 0 {
                        line.to_owned()
                    } else {
                        format!("{}{line}", indent_by_level(3))
                    })
                    .join("\n"),
                if comment.is_empty() { "" } else { "\n" }
            );

            // Builds command.
            let mut cmd = Command::new(env::var("CARGO").as_deref().unwrap_or("cargo"));
            cmd.arg("verify-pallet");

            // JSON diagnostics are easier to parse.
            // Ref: <https://doc.rust-lang.org/cargo/reference/external-tools.html#json-messages>
            // Ref: <https://doc.rust-lang.org/rustc/json.html>
            cmd.arg("--message-format=json");

            // Sets cargo `--target-dir` arg.
            let mut target_dir = env::var("CARGO_TARGET_DIR")
                .map(PathBuf::from)
                .unwrap_or_else(|_| {
                    env::current_dir()
                        .expect("Expected valid current dir")
                        .join("target")
                })
                .join("bench");
            target_dir.push(format!("{pallet_name}/{fixture_kind}"));
            cmd.arg("--target-dir");
            cmd.arg(target_dir);

            // Set target crate by manifest path.
            let manifest_path = PathBuf::from(format!("{bench_path}/{fixture_kind}/Cargo.toml"));
            cmd.arg("--manifest-path");
            cmd.arg(manifest_path);

            // Retrieves output.
            let start_time = Instant::now();
            let out = cmd.output().expect("Failed to run cmd");
            let stdout = String::from_utf8_lossy(&out.stdout);
            if !out.status.success() {
                panic!("Failed to analyze: {bench_path}/{fixture_kind}");
            }

            // Parses results.
            let results = parse_results(&stdout);

            // Analyzes and outputs results.
            let mut n_passed_for_pallet = 0;
            let mut n_failed_for_pallet = 0;
            let mut n_true_positives_for_pallet = 0;
            let mut n_false_positives_for_pallet = 0;
            let mut n_false_negative_for_pallet = 0;
            for call in results.keys().sorted() {
                // Compares actual returned diagnostics to expected results (if any),
                // and tracks counts for "true positives" and "false positives", and "false negatives".
                let diagnostics = results
                    .get(call)
                    .expect(&format!("Expected entry for: {call}"));
                let empty = Vec::new();
                let expected_results = fixture.expected_results.get(call).unwrap_or(&empty);
                let n_expected = expected_results.len();
                let n_actual = diagnostics.len();
                let (n_true_positives, n_false_positives, n_false_negatives) =
                    compare_results(&diagnostics, &expected_results);

                // We pass if the verifier has no "false positives" and no "false negatives",
                // "true positives" are acceptable.
                let passed =
                    n_expected == n_actual && n_false_positives == 0 && n_false_negatives == 0;

                // Outputs results for pallet call `fn`.
                println!(
                    "{}{call} ... {}\n{}{} expected; {} found; \
                    {} true positive(s); {} false positive(s); {} false negative(s)",
                    indent_by_level(2),
                    if passed {
                        "ok".style(green)
                    } else {
                        "failed".style(red)
                    },
                    indent_by_level(3),
                    n_expected,
                    n_actual,
                    n_true_positives,
                    n_false_positives,
                    n_false_negatives,
                );

                // Updates totals for pallet variant.
                if passed {
                    n_passed_for_pallet += 1;
                } else {
                    n_failed_for_pallet += 1;
                }
                n_true_positives_for_pallet += n_true_positives;
                n_false_positives_for_pallet += n_false_positives;
                n_false_negative_for_pallet += n_false_negatives;
            }

            // Outputs results for pallet variant.
            let elapsed = start_time.elapsed();
            println!(
                "\n{}bench result: {}. {} passed; {} failed; {} \
                true positive(s); {} false positive(s); {} false negative(s); finished in {}.{}s\n",
                indent_by_level(2),
                if n_failed_for_pallet == 0 {
                    "ok".style(green)
                } else {
                    "failed".style(red)
                },
                n_passed_for_pallet,
                n_failed_for_pallet,
                n_true_positives_for_pallet,
                n_false_positives_for_pallet,
                n_false_negative_for_pallet,
                elapsed.as_secs(),
                elapsed.subsec_millis()
            );

            // Updates totals for whole benchmark suite.
            n_passed_total += n_passed_for_pallet;
            n_failed_total += n_failed_for_pallet;
            n_true_positives_total += n_true_positives_for_pallet;
            n_false_positives_total += n_false_positives_for_pallet;
            n_false_negative_total += n_false_negative_for_pallet;
            total_elapsed += elapsed;
        }
    }

    // Outputs aggregated results for whole benchmark suite.
    println!(
        "\ntotal bench result: {}. {} passed; {} failed; {} filtered out; {} true positive(s); \
        {} false positive(s); {} false negative(s); finished in {}.{}s\n",
        if n_failed_total == 0 {
            "ok".style(green)
        } else {
            "failed".style(red)
        },
        n_passed_total,
        n_failed_total,
        n_filtered_out,
        n_true_positives_total,
        n_false_positives_total,
        n_false_negative_total,
        total_elapsed.as_secs(),
        total_elapsed.subsec_millis()
    );
}

/// Describes a collection of test fixtures to run.
/// See [FixtureGroup], [Fixture] and [FixtureKind].
fn fixtures() -> Vec<FixtureGroup> {
    vec![
        // Tests detection of possible "integer cast overflows" using `pallet-multisig`.
        FixtureGroup {
            pallet_name: "multisig",
            sdk: Fixture {
                comment: "\"possible integer cast overflow\" at `multisig/sdk/src/lib.rs:545`, \
                affects `approve_as_multi` and `as_multi`",
                expected_results: HashMap::from([
                    (
                        Call::new_dispatchable("approve_as_multi".to_owned()),
                        vec![ExpectedDiagnostic {
                            message: "possible attempt to cast with overflow",
                            location: "src/lib.rs:545",
                        }],
                    ),
                    (
                        Call::new_dispatchable("as_multi".to_owned()),
                        vec![ExpectedDiagnostic {
                            message: "possible attempt to cast with overflow",
                            location: "src/lib.rs:545",
                        }],
                    ),
                ]),
            },
            edit: Fixture {
                // Removes `usize to u16` integer cast (`as` conversion) for `m.approvals.len(): usize`
                // at `multisig/edit/src/lib.rs:545`.
                // Then uses `u16 to usize` integer cast instead for related comparisons to `threshold: u16` at
                // `multisig/edit/src/lib.rs:547` and `multisig/edit/src/lib.rs:554`.
                comment:
                    "fixes \"possible integer cast overflow\" at `multisig/edit/src/lib.rs:545`",
                expected_results: HashMap::new(),
            },
        },
        // Tests detection of possible panics using `pallet-preimage`.
        FixtureGroup {
            pallet_name: "preimage",
            sdk: Fixture {
                comment: "no diagnostics expected",
                expected_results: HashMap::new(),
            },
            edit: Fixture {
                // Replaces `debug_assert!` with `assert!` at `preimage/edit/src/lib.rs:439` causing a potential panic.
                comment: "introduces possible panic by replacing `debug_assert!` with `assert!` \
                    at `preimage/edit/src/lib.rs:439`",
                expected_results: HashMap::from([
                    (
                        Call::new_dispatchable("unnote_preimage".to_owned()),
                        vec![ExpectedDiagnostic {
                            message: "possible preimage request counter at zero?",
                            location: "src/lib.rs:439",
                        }],
                    ),
                    (
                        Call::new_dispatchable("unrequest_preimage".to_owned()),
                        vec![ExpectedDiagnostic {
                            message: "possible preimage request counter at zero?",
                            location: "src/lib.rs:439",
                        }],
                    ),
                ]),
            },
        },
        // Tests detection of possible arithmetic overflow using `pallet-treasury`.
        FixtureGroup {
            pallet_name: "treasury",
            sdk: Fixture {
                comment: "\"possible attempt to add with overflow\" at:\n\
                    - `treasury/sdk/src/lib.rs:637` which affects `spend`\n\
                    - `treasury/sdk/src/lib.rs:511` which affects `spend_local`",
                expected_results: HashMap::from([
                    (
                        Call::new_dispatchable("spend".to_owned()),
                        vec![ExpectedDiagnostic {
                            message: "possible attempt to add with overflow",
                            location: "src/lib.rs:637",
                        }],
                    ),
                    (
                        Call::new_dispatchable("spend_local".to_owned()),
                        vec![ExpectedDiagnostic {
                            message: "possible attempt to add with overflow",
                            location: "src/lib.rs:511",
                        }],
                    ),
                ]),
            },
            edit: Fixture {
                // Adds `Error::IndexOverflowLimit` variant at `treasury/edit/src/lib.rs:411`,
                // Then adds `ensure!` conditions (i.e. `x < u32::MAX`) that preclude add overflows for:
                // - `index` in `spend` at `treasury/edit/src/lib.rs:629`
                // - `proposal_index` in `spend_local` at `treasury/edit/src/lib.rs:504`
                comment: "fixes \"possible attempt to add with overflow\" at:\n\
                    - `treasury/edit/src/lib.rs:637` which affects `spend`\n\
                    - `treasury/edit/src/lib.rs:511` which affects `spend_local`",
                expected_results: HashMap::new(),
            },
        },
    ]
}

// Compares actual returned diagnostics to expected results (if any),
// and returns counts for "true positives" and "false positives", and "false negatives" as a tuple.
fn compare_results(
    diagnostics: &[DiagnosticJSON],
    expected_results: &[ExpectedDiagnostic],
) -> (usize, usize, usize) {
    // Simplifies the diagnostic JSON structure.
    let simple_diagnostics: Vec<_> = diagnostics
        .iter()
        .map(|diag| {
            let Some(serde_json::Value::String(warning)) = diag.get("message") else {
                unreachable!("Expected `message` key for diagnostic");
            };
            let Some(serde_json::Value::String(msg)) = diag.get("rendered") else {
                unreachable!("Expected `rendered` key for diagnostic");
            };
            (warning, msg)
        })
        .collect();
    match (expected_results.is_empty(), simple_diagnostics.is_empty()) {
        // We don't expect diagnostics, and don't receive any.
        // Essentially, a perfect performance from both the developer and the verifier.
        (true, true) => (0, 0, 0),
        // We don't expect diagnostics, but have them.
        // Essentially, all the diagnostics are false positives.
        (true, false) => (0, simple_diagnostics.len(), 0),
        // We expect diagnostics, but don't have them.
        // Essentially, the expected results are all false negatives.
        (false, true) => (0, 0, expected_results.len()),
        // We expected diagnostics and have them.
        (false, false) => {
            let mut unmatched_diagnostics = simple_diagnostics.clone();
            let mut n_true_positives = 0;
            let mut n_false_negatives = 0;
            for expected in expected_results {
                let mut found_match = false;
                unmatched_diagnostics.retain(|(message, rendered)| {
                    if found_match {
                        return true;
                    }
                    let is_match =
                        message.contains(expected.message) && rendered.contains(expected.location);
                    if is_match {
                        found_match = true;
                    }
                    !is_match
                });
                if found_match {
                    n_true_positives += 1;
                } else {
                    n_false_negatives += 1;
                }
            }
            let n_false_positives = unmatched_diagnostics.len();
            (n_true_positives, n_false_positives, n_false_negatives)
        }
    }
}

/// Describes a test for an "sdk" and "edited" version of a pallet.
struct FixtureGroup {
    pallet_name: &'static str,
    sdk: Fixture,
    edit: Fixture,
}

/// Describes a single test on a single version of a pallet.
struct Fixture {
    /// A comment that describes the purpose or intent of the test.
    comment: &'static str,
    /// Describes the expected results of the analysis for a pallet `fn`.
    /// Any `fn` ommitted in this map are treated as if they're expected to have no diagnostics.
    /// See [Call].
    expected_results: HashMap<Call, Vec<ExpectedDiagnostic>>,
}

#[derive(Debug)]
struct ExpectedDiagnostic {
    message: &'static str,
    location: &'static str,
}

/// Kind of the test fixture.
enum FixtureKind {
    SDK,
    Edit,
}

// Parses and returns `cargo verify-pallet` results.
fn parse_results(stdout: &str) -> HashMap<Call, Vec<DiagnosticJSON>> {
    let mut current_call = None;
    let mut results = HashMap::new();
    for line in stdout.lines() {
        if line.starts_with(DISPATCHABLE_PREFIX) {
            let call = Call::new_dispatchable(extract_name(line, DISPATCHABLE_PREFIX));
            results.insert(call.clone(), Vec::new());
            current_call = Some(call);
            continue;
        }
        if line.starts_with(PUB_ASSOC_FN_PREFIX) {
            let call = Call::new_pub_assoc_fn(extract_name(line, PUB_ASSOC_FN_PREFIX));
            results.insert(call.clone(), Vec::new());
            current_call = Some(call);
            continue;
        }

        if current_call.is_some() && line.contains("\"compiler-message\"") {
            if let Some(diagnostic) = extract_diagnostic(line) {
                let call = current_call.as_ref().expect("Expected a `Call`");
                match results.get_mut(&call) {
                    Some(diags) => diags.push(diagnostic),
                    None => {
                        results.insert(call.clone(), vec![diagnostic]);
                    }
                }
            }
        }
    }
    results
}

const DISPATCHABLE_PREFIX: &str = "Analyzing dispatchable:";
const PUB_ASSOC_FN_PREFIX: &str = "Analyzing pub assoc fn:";

type DiagnosticJSON = serde_json::Map<String, serde_json::Value>;

/// Extracts name of analyzed `fn` from `pallet-verifier` output.
fn extract_name(line: &str, prefix: &str) -> String {
    line.strip_prefix(prefix)
        .expect("Expected prefix")
        .trim()
        .chars()
        .skip(1)
        .take_while(|c| *c != '`')
        .join("")
}

/// Extracts diagnostics from JSON text.
/// Ref: <https://doc.rust-lang.org/cargo/reference/external-tools.html#json-messages>
/// Ref: <https://doc.rust-lang.org/rustc/json.html>
fn extract_diagnostic(line: &str) -> Option<DiagnosticJSON> {
    let serde_json::Value::Object(data) = serde_json::from_str::<serde_json::Value>(line).ok()?
    else {
        return None;
    };
    let serde_json::Value::String(reason) = data.get("reason")? else {
        return None;
    };
    if reason != "compiler-message" {
        return None;
    }
    let serde_json::Value::Object(msg) = data.get("message")? else {
        return None;
    };
    let serde_json::Value::String(msg_type) = msg.get("$message_type")? else {
        return None;
    };
    if msg_type != "diagnostic" {
        return None;
    }
    let serde_json::Value::Array(spans) = msg.get("spans")? else {
        return None;
    };
    (!spans.is_empty()).then_some(msg.clone())
}

impl std::fmt::Display for FixtureKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::SDK => "sdk",
                Self::Edit => "edit",
            },
        )
    }
}

/// Name and kind of pallet `fn`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum Call {
    Dispatchable(String),
    Hook(String),
    PubAssocFn(String),
}

impl Call {
    /// Creates a new [Call] instance.
    fn new(name: String, kind: CallKind) -> Self {
        match kind {
            CallKind::Dispatchable => Call::Dispatchable(name),
            CallKind::Hook => Call::Hook(name),
            CallKind::PubAssocFn => Call::PubAssocFn(name),
        }
    }

    /// Creates a new [Call] instance of the [CallKind::Dispatchable] kind.
    fn new_dispatchable(name: String) -> Self {
        Self::new(name, CallKind::Dispatchable)
    }

    /// Creates a new [Call] instance of the [CallKind::PubAssocFn] kind.
    fn new_pub_assoc_fn(name: String) -> Self {
        Self::new(name, CallKind::PubAssocFn)
    }

    /// Returns the name of the pallet `fn`.
    fn name(&self) -> &str {
        match self {
            Self::Dispatchable(name) | Self::Hook(name) | Self::PubAssocFn(name) => name,
        }
    }
}

impl Ord for Call {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Call::Dispatchable(_), Call::Dispatchable(_))
            | (Call::Hook(_), Call::Hook(_))
            | (Call::PubAssocFn(_), Call::PubAssocFn(_)) => Ord::cmp(self.name(), other.name()),
            (Call::Dispatchable(_), Call::Hook(_)) => Ordering::Less,
            (Call::Dispatchable(_), Call::PubAssocFn(_)) => Ordering::Less,
            (Call::Hook(_), Call::PubAssocFn(_)) => Ordering::Less,
            (Call::Hook(_), Call::Dispatchable(_)) => Ordering::Greater,
            (Call::PubAssocFn(_), Call::Dispatchable(_)) => Ordering::Greater,
            (Call::PubAssocFn(_), Call::Hook(_)) => Ordering::Greater,
        }
    }
}

impl PartialOrd for Call {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: `{}`",
            match self {
                Self::Dispatchable(_) => "dispatchable",
                Self::Hook(_) => "hook",
                Self::PubAssocFn(_) => "pub assoc fn",
            },
            self.name()
        )
    }
}

/// Returns indenting space for given level
///
/// (e.g. 2 spaces for level 1, 4 space for level 2 e.t.c).
fn indent_by_level(level: u8) -> String {
    (0..level * 2).map(|_| " ").join("")
}
