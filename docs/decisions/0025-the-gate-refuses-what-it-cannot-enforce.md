# 0025: The gate refuses what it cannot enforce

Date: 2026-10-04. Status: decided. Follows an outside review of commit f5fca63.

## Decision

A gate run that cannot enforce every row is refused, exit 2. A missing check, which includes every `cplusp-` check when the plugin is not loaded, is such a run. The flags of a compile database are judged like the flags after `--`. A response file is refused, because the gate cannot read it. A diagnostic pragma, or a `system_header` pragma, is a finding like `NOLINT`, in the given files and in the headers they include outside the system paths. The rows `recursion` and `global_state` move to the prover. Dafny demands `decreases` and `modifies`, and no clang-tidy check reads a contract.

## Why

The review ran nine snippets the gate accepted, and reproduced each. The worst was not a missing pattern. Without the plugin, or through a compile database, the gate skipped most of its rows and still printed `ok`. A bot and a CI job read a zero exit as a pass. A gate that is not sure must say so with its exit code, never with a warning. The two unbuilt checks were the standing reason that every run carried a warning. They were never the right place for the rule. The prover reads the contract, the gate does not.

## What changes

The gate command, its tests and fixtures, decision 0014 extended. The two rows change stage, so the policy counts 56 gate rows. The soundness map records the review's wider point under gap 2. The gate is a list of spellings. Refusing what it does not understand is a later design step. The remaining findings of the review, pattern holes and a core postcondition, follow in their own rounds.
