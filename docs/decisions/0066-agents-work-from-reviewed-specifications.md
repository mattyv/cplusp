# 0066: The agents work from reviewed specifications, and the reviewer tries to break them

Date: 2026-10-08. Status: decided. Applies the workflow of 0065 to the agents of this repository.

## Decision

- The coder implements against the reviewed requirements, contracts and tests. Together they are the specification. The coder reads the section "Whole-program development" of the Dafny skill before it starts. It never changes a requirement, a contract or a test. When they conflict, or a test cannot be met, it reports the conflict.
- The reviewer decides each change to a requirement, a contract or a test. Fable writes the change.
- The reviewer tries to break each contract and each Verus `ensures` that a change adds or relies on. It writes deliberately wrong implementations, such as an empty result, a constant, a missed update, wrong handling of duplicates or an error of one. It runs the prover on each. The contract must reject each one. The reviewer also shows that intended inputs satisfy the preconditions. These checks find weak contracts. They do not prove that a contract is complete.
- Work goes in small increments. Each increment is proved before the next is built on it. When a proof gets hard, the data structures or the helper boundaries change. A reviewed contract never gets weaker to make a proof pass.

## Why

An outside review found that the agent files still called the failing tests the whole specification. It also found that the coder did not read the skill that 0065 updated. So the workflow of 0065 was written down but not followed. The report of 0065 cites studies in which buggy implementations and mutation checks exposed weak specifications. Other studies in it found that joint development of code and proof reached more targets. Those results are from other systems and from small studies. They are a reason to try the method here, not a measure of its payoff.

## What changes

`.claude/agents/coder.md`, `.claude/agents/reviewer.md`, `CLAUDE.md` and the skill say the rules above. Useful diagnostics from the prover, the second part of the same review, are the next slice of the translator, with their own decision.
