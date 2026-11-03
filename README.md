# cplusp

cplusp checks contracts on a restricted subset of C++. It is built for a coding
loop in which an LLM writes a function, runs the checker, and repairs the code
or reports a limit.

Contracts are comments above the function. This one requires ordered bounds and
promises a result inside them:

```cpp
//@ requires lo <= hi
//@ ensures lo <= result && result <= hi
int32_t clamp(int32_t x, int32_t lo, int32_t hi);
```

The [complete example](crates/cplusp/tests/fixtures/model-clamp.cpp) also specifies
which value to return in each case. A contract must describe the behavior you
want. A proof cannot fill in a missing requirement.

## Start here

| I want to… | Read |
| --- | --- |
| Build the tool and run my first proof | [Use cplusp](docs/getting-started.md) |
| Fix a bug or extend the checker | [Contribute to cplusp](docs/contributing.md) |
| Understand what a successful proof establishes | [Proof FAQ](docs/formal-proof-faq.md) |
| See the current trust assumptions and known gaps | [Soundness](docs/soundness.md) |

## What the commands check

1. `gate` checks the source and build flags against the policy. A pass means the
   gate found no violation. It does not establish the function's contract.
2. `model` translates supported C++ and its contracts into Dafny. It runs no
   proof and does not run the full gate.
3. `prove` runs the gate, translates the source, and asks Dafny to prove the
   generated model. Use this command for the complete check.

After [building the tool](docs/getting-started.md#build), run this from the repository root:

```sh
./target/debug/cplusp prove --plugin target/plugin/libcplusp.so \
  crates/cplusp/tests/fixtures/model-clamp.cpp -- -std=c++23 -ffp-contract=off
```

A successful run ends with `ok: proved` and exits 0. Review any `Trusted:` and
`Axiom:` lines too. They name assumptions used by the proof.

## Proof scope

cplusp is under development. It proves properties of a Dafny model under the
function's preconditions and the model's assumptions. Applying that result to
C++ also depends on the translation, trusted code, compiler and target.

Verus checks the Rust core against its specifications. Those proofs do not
establish that every translation rule preserves C++ behavior. The project uses
regression tests and divergence cases to examine that gap. See
[soundness](docs/soundness.md) before relying on a result.

The current CLI checks the files you name. It has no automatic changed-caller
tracking or incremental proof cache. Recheck affected callers when a contract
changes. Trusted bodies, plain code and unverified callers remain outside the
proof of a verified function.

## Reference

- [Examples](examples/README.md): C++ contracts, companion specifications and handwritten models.
- [Contract and translation guide](skills/cplusp-dafny/SKILL.md): supported forms and the agent workflow.
- [Policy reference](docs/policy.md): rules, overrides and gate diagnostics.
- [Default policy](policy/cplusp-policy.yaml): the rule data shipped with the tool.
- [Design notes](docs/plan.md): architecture, original proposals and implementation history.
- [Decisions](docs/decisions/README.md): why behavior changed. Later decisions amend earlier ones.
- [CI checks](.github/workflows/check.yml): format, lint, tests and Verus verification.

## License

MIT licensed. See [LICENSE](LICENSE).
