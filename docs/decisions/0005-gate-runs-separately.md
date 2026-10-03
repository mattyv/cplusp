# 0005: The gate runs apart from a team's own clang-tidy

Date: 2026-10-03. Status: decided.

## Decision

The gate is its own clang-tidy run with its own generated config, its own loaded plugin and its own pinned clang-tidy. It reads the team's compile_commands.json and never reads or edits the team's `.clang-tidy`.

## Why

The gate must fail only on policy rows. A team's config could add noise or switch a required check off. Teams run clang-tidy 16 to 20 and must not have to change.

## What changes

One extra CI job. A container image and a GitHub Action that carry clang-tidy 18.
