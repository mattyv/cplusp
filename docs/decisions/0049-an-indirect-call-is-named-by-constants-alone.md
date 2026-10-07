# 0049: An indirect call is named by constants alone

Date: 2026-10-07. Status: decided. Amends 0048 on which indirect call the row `function_pointers` refuses.

## Decision

Each value that can reach the callee of an indirect call must be a function constant, a vtable or a constant table of decision 0037. Only then does the call have a name. A pointer from a parameter, from `this`, from a call, or from memory that a call can write has no name. Verified code that runs a call through such a pointer gets a finding of `function_pointers` at the call, as 0048 says. The gate gives no excuse to a pointer that the caller holds.

A verified function that takes a pointer to a function then has two findings: the type at its declaration, and the call in its body. Both are uses of a pointer to a function.

## Why

The review of the 0048 green step found three ways past the check. Each came through an excuse. An argument of the caller made the result of a call look named. A pointer that a parameter held counted as the caller's, but the check looked at the caller only for library code. A store through an argument was not followed. Each excuse is a list, and each review can make it longer. An analysis that cannot finish refuses, decision 0036.

## What changes

The check drops its excuses. The sample pair of `function_pointers` gets a mark at each call through a pointer that has no name. A fixture holds the three ways. An abbreviated function template begins at its return type, so its marker and its contract are read.
