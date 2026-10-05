# 0032: The gate is an allowlist

Date: 2026-10-05. Status: decided. Amends 0016, which made one generic matcher check the gate's main check. Closes the ceiling that soundness gap 2 named.

## Decision

The gate refuses every construct it does not know. The policy carries a list of the AST node kinds that verified code may use: the statements, the expressions, the declarations and the types. A hand-written check, `cplusp-allowlist`, walks every node of a verified file and refuses a node of a kind that is not on the list. The finding names the row that claims the kind, when a row does. Otherwise it names the row `unlisted`, which says the construct is outside the subset and asks for a row.

A ban row whose construct is a whole node kind drops its matcher and names its kinds instead. A matcher stays only for a shape inside an allowed kind, such as a downcast inside `static_cast`, and so does every hand-written check. We seed the list from the node kinds that the sample pairs and the examples use today. Then we review it by hand, one kind at a time.

## Why

Sixty-one ban rows are a blocklist, and a blocklist leaks. Two outside reviews found twenty-four spellings the rows did not know, in two sittings. Each fix was one more matcher, and nothing says the next review finds none. An allowlist is sound by construction. A construct the list does not name cannot pass. The gate refuses a new C++ feature on the day the compiler adds it. The matcher rows and the checks then do the one thing a kind cannot say, which is a shape or a semantic rule. This is the design step soundness gap 2 deferred.

## What changes

The policy gains the list and the row `unlisted`. The plugin gains the check. The ban rows that are a whole kind lose their matcher. Every `allowed.cpp` and every example still passes, and every `banned.cpp` still fails on its lines under its row. That pair of facts is the test of the list. Plan section "One generic check, driven by the policy" says allowlist first, matchers second.
