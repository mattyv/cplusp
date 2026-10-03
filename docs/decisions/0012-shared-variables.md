# 0012: Variables other threads may change enter verified code only as values

Date: 2026-10-03. Status: proposed.

## Decision

A shared variable is never read or written directly in verified code. It arrives as a parameter or as the result of a trusted getter. The getter's contract states only what is true of every value ever stored. Each call may return a different value.

## Why

A per-function proof assumes nothing changes under it. A shared variable breaks that twice: a plain read is a data race, and two reads may differ.

## What changes

The `shared_variables` row. A known limit: lost updates are not caught. A read-then-write pair needs a trusted wrapper.
