# 0006: One policy file, decisions and detection together

Date: 2026-10-03. Status: decided.

## Decision

`cplusp-policy.yaml` holds one entry per row of the subset table. Each entry carries the decision and the checks that detect the construct. A team policy extends the default and may loosen a rule only with `loosened_because`. Every run prints what was loosened.

## Why

The table and the file stay one list. Hiding detection in the tool would be tidier for teams but harder to extend. Loosening with a visible reason beats a rule teams work around.

## What changes

`cplusp policy check`, `emit`, `show` and `doc`. The plan's table is generated from the file.
