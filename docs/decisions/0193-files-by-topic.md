# 0193: Files by topic

Date: 2026-10-25. Status: decided. Builds on 0121.

## Decision

The translator of the core, `crates/cplusp-core/src/model.rs`, becomes the folder `crates/cplusp-core/src/model/`. Each section of the old file is a file of its own, by its topic. The file `mod.rs` holds the summary of the proofs and names each file. Each name of the old file keeps its path `model::name`, so the shell and the tests do not change.

The move changes no rule, no contract and no proof. It moves the text and adds the lines that each file needs to see the others. `cargo verus verify` and the test suite give the same results before and after. The lemma `lemma_covers` in `contract.rs` gets the budget `rlimit(20)`, because it ran out of its default budget after the move. Its contract does not change.

The plugin `clang-tidy/CplusPModule.cpp` and the tests `crates/cplusp/tests/cli.rs` follow, each in a change of its own, with the same rule: move the text and change nothing else.

## Why

The file had 15,000 lines, and each decision added to it. A reviewer reads a change of one topic in one file of a few thousand lines. A section header was the only map. Each section already holds one topic, so the cut follows the headers.

## What changes

The core gets the folder `model/` with one file for each section. `docs/plan.md` names the folder where it named the file.
