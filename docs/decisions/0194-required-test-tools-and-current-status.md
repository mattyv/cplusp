# 0194: Required test tools and current status

Date: 2026-10-25. Status: decided. Amends the test reporting of 0010 and the status documentation of 0056.

## Decision

A test that needs clang-tidy or Dafny fails when that tool cannot run. The CLI tests and the divergence battery cannot silently omit the gate. An explicit `DAFNY` path must run successfully with `--version`. It cannot fall back to another installation.

GitHub runs the complete executable test suite and the Verus core proofs as separate jobs. The workflow uses the existing Rust, vstd and Dafny versions. It builds Verus from the same revision as vstd. Missing tools, failed installation and failed checks make the job fail.

The root README describes the current pipeline, trusted boundary and check commands. The design plan remains historical design material. The soundness map records the implemented translator and parser without treating semantic equivalence as proved.

## Why

The old CLI tests could report success after returning before they ran a required tool. The battery could omit the gate. The soundness map still described automatic translation and contract parsing as absent. Together these made the evidence harder to interpret.

## Scope

This changes test execution and documentation. It does not change translation rules, proof contracts, accepted C++ constructs or the roadmap. Application validation remains planned. The user has not decided to freeze feature development.
