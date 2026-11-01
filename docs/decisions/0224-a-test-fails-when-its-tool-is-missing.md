# 0224: A test fails when its tool is missing

Date: 2026-11-01. Status: decided. Amends the test reporting of 0010. It takes the first part of an earlier proposal on the branch `codex/reliable-checks-and-current-docs`, which that branch also numbered 0194.

## Decision

A test that needs clang-tidy or Dafny fails when that tool does not run. The message names the tool and how to get it. A `DAFNY` path must run `--version`, and no other install takes its place. The divergence battery fails the same way when clang-tidy does not run, so it cannot leave out the gate.

`CPLUSP_SKIP_TOOLS=1` is the only way to skip such a test. A person sets it on a machine with no tools. Without it, each skip in the tests is a failure.

## Why

The tests returned early when a tool was missing, and `cargo test` then said `ok`. So a machine with no Dafny reported a green suite that proved nothing. The change is in the two helper functions that find the tools, so each test keeps its form.
