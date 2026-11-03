# Contribute to cplusp

Start by [building the tool and running the proof examples](getting-started.md).
Then reproduce the behavior you want to change. A useful regression test shows
what the user should observe, including the exit status and diagnostic.

Read [CLAUDE.md](../CLAUDE.md) for the repository's contribution rules and agent
roles. This guide maps those rules to the code, tests and verification commands.

## Find the responsible layer

`prove` runs the gate, obtains the compiler's representation of the source,
translates it, and runs Dafny. Errors map back to C++ locations.

| Location | Responsibility | Evidence |
| --- | --- | --- |
| [clang-tidy/](../clang-tidy/) | Inspect C++ with Clang. Enforce gate checks and emit the translation input. | Rule samples and CLI fixtures. This C++ code is trusted. |
| [crates/cplusp/src/main.rs](../crates/cplusp/src/main.rs) | Load policy and build arguments. Run tools and report findings. | CLI tests. This Rust code is trusted. |
| [crates/cplusp-core/src/](../crates/cplusp-core/src/) | Define and implement policy, parsing, translation and verdict rules. | Verus proofs and core tests. |
| [crates/cplusp/src/model.rs](../crates/cplusp/src/model.rs) | Read plugin output and render Dafny with source locations. | Translation fixtures. This Rust code is trusted. |
| [crates/cplusp/src/prove.rs](../crates/cplusp/src/prove.rs) | Run Dafny and map its output to user diagnostics. | CLI fixtures and simulated tool failures. This Rust code is trusted. |
| [divergence/dafny/](../divergence/dafny/) | Record cases where C++ and a naive model disagree. Provide model support files. | The divergence battery and differential cases. |

Keep semantic rules in the core where Verus can check them. File I/O, process
execution and rendering remain trusted boundaries. A proof that implementation
matches specification does not establish that the specification matches C++.
Review that correspondence separately.

## Add the regression first

Choose the smallest case that exposes the defect:

| Change | Start here |
| --- | --- |
| Policy or gate check | [rules/](../rules/) and [CLI gate tests](../crates/cplusp/tests/cli/gate.rs) |
| Translation or contract handling | [CLI fixtures](../crates/cplusp/tests/fixtures/) and the matching module under [cli/](../crates/cplusp/tests/cli/) |
| Core rule | [Core tests](../crates/cplusp-core/tests/) and that rule's Verus specification |
| C++ behavior differs from its model | [Divergence cases](../divergence/dafny/cases/) and [battery tests](../crates/divergence/tests/battery.rs) |
| Tool launch or output handling | CLI tests with a controlled tool result |

Run the test before the fix. Confirm that it fails for the intended reason.
Keep reviewed requirements and contracts fixed while repairing the implementation.
If a requirement must change, document and review that change explicitly.

For a new construct, include an accepted case and a rejected case. Challenge a
functional contract with a deliberately wrong body. Also show that intended
inputs satisfy its preconditions. A contract that admits no input proves no
useful behavior.

Record behavior decisions in a new numbered file under [decisions/](decisions/README.md).
Update the index. Later decisions amend earlier ones, which remain unchanged.

## Run the checks

From the repository root, with `DAFNY` set as in the setup guide:

```sh
rustup component add rustfmt clippy
cargo fmt --all --check
cargo clippy --workspace --all-targets --locked -- -D warnings
cmake --build target/plugin
cargo test --workspace --locked
```

To run one CLI regression while working:

```sh
cargo test -p cplusp --test cli gate_keeps_database_option_values_that_name_the_source
```

Missing tools fail tests that require them. `CPLUSP_SKIP_TOOLS=1` allows a partial
run for local work. Report that run as partial. It does not replace the full suite.
`CPLUSP_PLUGIN` selects a test plugin path. It does not replace the CLI's
`--plugin` option.

Examples contain both handwritten Dafny models and C++ sources. A handwritten
model proving does not demonstrate that automatic translation accepts its C++.
See [Examples](../examples/README.md) for the separate checks.

## Verify the core

`cargo test` does not verify the Verus proofs. Use the Verus revision pinned by
the `vstd` dependency in [Cargo.toml](../crates/cplusp-core/Cargo.toml).
The [CI workflow](../.github/workflows/check.yml) contains the matching verifier build.

To reproduce that build, start from the cplusp repository root:

```sh
git clone https://github.com/verus-lang/verus.git target/verus
git -C target/verus checkout 11ed7501a8ba5160be537da21cca330dafbecb9b
```

Build the verifier and its standard library in the cloned source directory:

```sh
cd target/verus/source
rustup toolchain install 1.98.1 --profile minimal --component rustc-dev --component llvm-tools
./tools/get-z3.sh
export VERUS_Z3_PATH="$PWD/z3"
cargo build --release --locked
cargo run --release --locked -p cargo-verus -- build --release --manifest-path vstd/Cargo.toml
cd ../../..
```

Back at the cplusp root, verify the core:

```sh
./target/verus/source/target-verus/release/cargo-verus verify \
  --manifest-path crates/cplusp-core/Cargo.toml --locked
```

The repository requires zero verification errors before a commit. Do not weaken
a contract to make this check pass. If a tool cannot run, report the missing
validation explicitly.

## Review a change

Read the final diff as someone who did not write it. Check accepted inputs,
rejected inputs, failure exits and the assumptions the change introduces.
A timeout, compiler failure or unreadable tool result must never become success.

State what changed in behavior and why. List the tests and proofs actually run,
their results, and any checks that remain unavailable. Keep new trust assumptions
visible in [soundness](soundness.md) and the decision record.

## Maintain the documentation

Put executable instructions in [Use cplusp](getting-started.md), contribution
instructions here, and detailed policy rules in [the policy reference](policy.md).
Keep the [design notes](plan.md) explicit about proposals and implemented behavior.
Use the decision log to explain changes, rather than requiring new readers to
reconstruct the current workflow from its history.

When a command, diagnostic, tool version or supported form changes, update its
guide with the code. Check relative links and command paths. The STE checker
named in `CLAUDE.md` is supplied by that skill, not by this repository.
