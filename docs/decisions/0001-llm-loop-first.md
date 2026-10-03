# 0001: The tool serves the LLM coding loop first

Date: 2026-10-03. Status: decided.

## Decision

The bot runs `cplusp` as a command after it writes C++, reads the messages and fixes the code. Nothing runs automatically on save. CI runs the same command as a backstop.

## Why

The point is fast feedback to the bot, not a report to a human a day later. An automatic hook was considered and rejected: the bot should run the processes itself.

## What changes

Messages are written for a bot. Speed matters. PR annotations and the approval rule move to the end of the plan.
