# 0014: The gate refuses what it cannot judge

Date: 2026-10-03. Status: decided.

## Decision

The gate exits 2 instead of saying "no findings" in five cases:

- A file does not compile. Compiler errors named after a warning option count.
- `-p` names a directory without compile_commands.json.
- `-p` and trailing `--` flags are both given.
- A policy file lacks `rules`, or a rule or override carries a field it may not.
- An input file cannot be read.

A `NOLINT` comment is a finding. Project headers are judged. Checks that do not exist yet are named on stderr on every run.

## Why

The first review found six ways to get a quiet "ok" for code the gate should have refused. For a gate whose reader is an LLM, a quiet pass is the worst failure.

## What changes

Twelve tests. The refusals section of docs/policy.md.
