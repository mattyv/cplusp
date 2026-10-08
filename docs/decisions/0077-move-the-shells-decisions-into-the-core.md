# 0077: Move the decisions of the shell into the core

Date: 2026-10-08. Status: decided. Amends 0056 on what the shell holds.

## Decision

- The shell keeps only file I/O, process launch, the parsers of other tools and the text of messages. Each decision that can turn a wrong result into `ok: proved` moves into the Verus core, with its proof.
- The order is by the harm that a defect can do:
  1. The verdict of `cplusp prove`. The core decides `proved`, `not proved` or `the tool failed`. It reads four facts from the shell. They are the exit status of Dafny, the counts of its summary, the number of error lines, and the refusals of the translator. The core proves a rule for `proved`. Dafny must exit with success, and its summary must have zero errors and zero time-outs. No error line can be present, and the translator must refuse nothing.
  2. The printer of the Dafny model. The core makes the text from the verified model, and it proves that the text has the meaning of the model.
  3. The contract lexer and the names. The core cuts a contract line into tokens and makes each Dafny name. It proves that the cut and the names keep the meaning of the text.
- A step that only formats text, or only helps a test, stays in the shell. A higher count of verified lines is not the goal.
- The verdict comes first, because it is small and it guards the claim directly. The printer and the lexer follow `radix_find`, decision 0072.

## Why

An outside review found that the share of verified Rust could be higher. The useful measure is different: how much code can turn a wrong result into `proved`. Today the verdict is ten lines of the shell, and a defect there would pass each proof of the core. The printer is larger, and a defect there makes Dafny prove a program that is not the model.

## What stays trusted

The plugin, which reads C++ through Clang, stays a trusted edge in C++. The match of C++ meaning to Dafny meaning stays a claim that the battery and the sample pairs support, not a proof. A trusted function of the shell keeps its contract as an assumption until its body moves into the core. `docs/plan.md` lists each trusted edge.
