# C+P

C+P checks contracts on a restricted subset of C++. It uses Clang to read the source, a Rust core verified with Verus to construct a model, and Dafny to prove that model.

This is a research tool. A successful proof applies to the contracts and assumptions of that run. It does not establish that a program meets an unstated requirement, or that the translation preserves every detail of C++ execution.

## Current implementation

`cplusp prove` runs the gate, automatic translation, and Dafny. It reports failures at C++ source locations. `cplusp model` emits the model without proving it. `cplusp gate` checks the policy without proving contracts.

The translator handles parts of integer arithmetic, control flow, sequences, objects, templates, ownership and floating point. Support is specific to each construct and use. An accepted policy row alone does not establish that a function can be translated or proved. Unsupported forms must be refused.

| Part | Responsibility | Assurance boundary |
| --- | --- | --- |
| `clang-tidy/` | Read Clang trees, check policy, lifetimes, aliasing and effects, and emit JSON | Trusted C++ implementation, checked by regression tests |
| `crates/cplusp-core/` | Parse contracts, construct models, check policy and compiler flags, read Dafny results | Verus proves specified properties of these operations |
| `crates/cplusp/` | Read files and JSON, render Dafny, run tools, map diagnostics | Trusted Rust implementation, checked by regression tests |
| `crates/divergence/` | Compare C++ with hand-written models and test known semantic differences | Execution evidence for the cases and inputs tested |

The core's proofs include agreement with its translation rules and refusal of unknown nodes. They do not prove that those rules preserve C++ behaviour. The Clang extraction, Dafny rendering, library models, compiler, prover, solver and execution environment remain part of the trusted boundary. Requirements and trusted contracts also need review.

## Build and check

The full test environment is Ubuntu 24.04 with Clang/clang-tidy 18, GCC, CMake, Ninja, Python 3 for Dafny's generated differential drivers, and Dafny 4.11.0. Rust is pinned by `rust-toolchain.toml`. The Verus source revision is `11ed7501a8ba5160be537da21cca330dafbecb9b`, matching the `vstd` dependency.

[The Checks workflow](.github/workflows/check.yml) records installation and execution commands. It runs two separate jobs: the C++/Dafny regression suite and the Verus core proofs. Both must succeed for a complete check. A job that cannot install or run a tool fails.

With those tools installed, run from the repository root:

```sh
cmake -S clang-tidy -B target/plugin -G Ninja
cmake --build target/plugin
cargo test --workspace --locked
cargo verus verify --manifest-path crates/cplusp-core/Cargo.toml --locked
```

Set `DAFNY` to its executable if it is not on PATH or at `/opt/dafny/dafny/dafny`. Set `CPLUSP_PLUGIN` if the plugin is not at `target/plugin/libcplusp.so`. A missing tool, a broken explicit `DAFNY` path, or a missing plugin fails the tests that require it. It cannot count as a successful skipped check.

To run the Rust core's executable tests on a machine without Clang and Dafny:

```sh
cargo test -p cplusp-core --locked
```

That is a partial test run. It does not run Verus proofs or establish that the C++/Dafny pipeline works.

## Evidence and next decisions

The CLI regression tests exercise automatic translation and proof success, rejection and refusal paths. The examples and divergence battery also contain hand-written Dafny. A hand-written model that verifies is not evidence that automatic translation of its C++ succeeds.

[The application validation plan](docs/end-to-end-validation-plan.md) remains planned work. It defines independent executable checks, fixed-contract mutations, maintenance changes and cost measurements. Example pass counts and Verus proof counts do not substitute for those application results.

Feature scope remains open. This change does not freeze the roadmap or remove existing capabilities.

## Documentation

- [Formal proof FAQ](docs/formal-proof-faq.md): what a proof establishes and what must remain explicit.
- [Soundness map](docs/soundness.md): assumptions, known gaps and the current translation boundary.
- [Policy format](docs/policy.md): policy files and team overrides.
- [Decision log](docs/decisions/README.md): the history of individual changes.
- [Design plan](docs/plan.md): original design and accumulated implementation notes. Historical milestones and proposals are not a current support checklist.
- [C+P skill](skills/cplusp-dafny/SKILL.md): writing and reviewing specifications.
