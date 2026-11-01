# cplusp

cplusp is C++ with one plus removed, and with proof. It limits C++ that an LLM writes to a subset that a prover can check, and then it proves the code against its contracts.

- The **gate** is a clang-tidy plugin and a Rust driver. It refuses each construct that the policy does not allow, and each finding names its rule.
- The **translator** turns the functions of a file and their `//@` contract lines into Dafny. Each rule of the translation is a Verus spec function, and Verus proves that the code does what the spec says.
- **`cplusp prove`** runs the gate, the translator and Dafny. It reports `Not provable:` (no rule yet) or `Not proved:` (the proof fails) at the C++ line, or `ok: proved`.

All 77 programs in `examples/` prove end to end.

## Build

You need these tools:

- Rust from `rust-toolchain.toml`.
- clang-tidy 18, clang 18, `libclang-18-dev` and `llvm-18-dev` (Ubuntu 24.04 apt), and CMake with Ninja.
- Dafny 4.11.0.
- Verus at the commit that `crates/cplusp-core/Cargo.toml` gives for `vstd`.

```
cmake -S clang-tidy -B target/plugin -G Ninja && cmake --build target/plugin
cargo build
```

## Run

```
cplusp gate  --plugin target/plugin/libcplusp.so FILE.cpp -- -std=c++23 -ffp-contract=off
cplusp prove --plugin target/plugin/libcplusp.so FILE.cpp -- -std=c++23 -ffp-contract=off
cplusp policy check
```

## Test and prove

```
DAFNY=/path/to/dafny cargo test --workspace
cd crates/cplusp-core && cargo verus verify
```

A test that needs clang-tidy or Dafny fails when that tool does not run, decision 0224. Set `CPLUSP_SKIP_TOOLS=1` to skip those tests. `CPLUSP_PLUGIN` names a plugin other than `target/plugin/libcplusp.so`. `.github/workflows/check.yml` runs the same checks on each push.

## Layout

- `crates/cplusp-core`: the Verus core. It has the policy, the contract parser and the translator, with their proofs.
- `crates/cplusp`: the driver. It does file I/O, launches the tools, parses YAML and prints the Dafny text. This is a trusted edge.
- `clang-tidy/`: the plugin, with the gate checks and the `cplusp-tree` check that writes each function for the core. This is a trusted edge.
- `policy/cplusp-policy.yaml`: the policy. Each rule the gate enforces has a sample pair in `rules/<id>/`.
- `examples/`: programs that prove. `divergence/`: the cases where a naive model of C++ in Dafny is wrong.
- `skills/cplusp-dafny/SKILL.md`: the guide for the LLM that writes the C++ and the contracts.

## Docs

- `docs/plan.md`: the design and the trusted edges.
- `docs/policy.md`: the format of the policy file.
- `docs/soundness.md`: each gap between C++ and the proof, and its status.
- `docs/decisions/`: the decision log. A decision is never edited. A newer file amends it.
- `CLAUDE.md`: how a change happens. The failing test comes first, then the green step, then a review.

## License

MIT, see `LICENSE`.
