# Examples

One folder per row of the policy that verified code may use: every `allow`, `restrict` and `trusted_only` row. Each shows the C++ as the bot should write it under the row, and the Dafny the bot writes for it by hand, decision 0017. The battery under `divergence/` shows where a naive model goes wrong. This folder shows the right way, one row at a time.

Each folder has:

- `example.cpp`: C++ under the row, with its `//@` contract. It passes the gate.
- `example.dfy`: the Dafny model of it, under the rules in `skills/cplusp-dafny/SKILL.md`. It verifies.
- `trusted.cpp`: for a `trusted_only` row only. The trusted function that uses the construct, behind the contract `example.cpp` declares. The gate refuses it under that row, which shows the construct is there. The prover never reads it. `example.cpp` holds the declaration with the contract and a verified caller.

The test `every_row_the_bot_may_use_has_an_example` in `crates/divergence` runs the gate on every `example.cpp` and `trusted.cpp`, and Dafny on every `example.dfy`. A contract in an example is a real one: it says what the function promises, never only that it returns.
