# 0007: The prover is a plug-in

Date: 2026-10-03. Status: decided.

## Decision

Any prover works if its adapter meets the interface in the plan: contracts in, verdicts with C++ locations out, no prover-specific hints from the bot. Dafny and VeriFast are the candidates. The thin slice runs one function through both by hand and picks the first to build. A second comes later as a cross-check. Verus is plan C.

## Why

VeriFast's C++ frontend lacked templates in 2022 and a 2026 study found 31% LLM success on its specs. Dafny has the automation and the training data. Neither is certain, so the design must not depend on the choice.

## What changes

The Prover interface section. The thin slice starts with a by-hand comparison. VeriFast is no longer named as the backend.
