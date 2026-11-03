# 0232: Repeated findings share their message

Date: 2026-11-03. Status: decided. Builds on 0155 and 0229.

## Decision

Human-readable gate output groups findings by the exact rule and message.
Each group prints the existing `Not provable:` line at its first location.
It then prints up to two `  Also at: FILE:LINE` lines. If more locations remain,
it prints `  N more locations.` with the number omitted.
Groups and their locations retain the current first-seen order after sorting
and duplicate removal. Different messages from one rule remain separate groups.
Different rules remain separate groups even when their messages match.

If any group omits locations, the output ends with one line:

```
All findings: run cplusp gate --json with the same inputs, policy, plugin and compiler flags.
```

The output has no footer when it shows every location. The gate called by `prove`
uses the same rendering. This change adds no option. `gate --json` retains
every finding, its fields, its order and its existing format. Policy decisions,
exit codes and tool failures do not change. A clean gate still prints
`ok: no findings`.

## Why

A smoke test against an existing header-only library produced many copies of
long refusal messages. Those copies obscured the distinct unsupported forms.
Showing each cause once keeps the next action visible. The JSON route retains
the complete evidence for tooling and detailed inspection.

## What changes

Only the shell's presentation changes. The gate still judges every finding.
This rendering has no Verus proof because text output belongs to the trusted
shell. CLI tests check repeated causes, distinct messages from the same rule,
the gate inside `prove`, complete JSON output and the footer condition.
