# 0190: Marks that hold of their own table

Date: 2026-10-25. Status: decided. Builds on 0090, 0095, 0188 and 0189. Changes how the core marks a member function pure, decision 0095. The review of 0189 found that two passes of the marks no longer agree with the table that the translator reads.

## Decision

The core marks a member function pure when its body is a pure body and its contract has a model, as 0095 says. Since 0189, a body is pure or not by the marks too, because a call of a plain member function reads them. So the core now finds the marks as follows:

- It starts with each member function marked pure. A member with no function of the file keeps its own mark, decision 0188.
- It marks the members again from the marks before, with the rule of 0095. It does this until a pass changes no mark, and at most once for each member and once more.

Then each mark holds of the table that the translator reads. A contract that calls a marked member calls a function that the model has. A call of a plain member function reads the same marks as the contracts that call its caller.

A requires line can call a member function that calls the function of the line, as `get()` with `//@ requires ok()` and `ok()` that calls `get()`. That is a cycle of functions. Dafny then cannot prove that the functions end. The sentence is `the prover cannot show that this ends.` It stands at the requires line, and at the line of the function that calls back.

## Why

Before 0189, a body was pure or not with no regard to the marks. Then two passes were enough: one for the bodies and one for the contracts. Since 0189, the body of a member function depends on the marks of the plain member functions that it calls. A pass that reads other marks than the final table can mark a member that the final table cannot translate as pure. Dafny then gets a call of a function that the model does not have. The review found two such cases. In one, a contract got a resolution error of Dafny where it had a sentence of the translator. In the other, a contract could not call a member function that 0189 lets it call. A table whose marks hold of their own table has no such case.

## What changes

The core replaces the two passes of `spec_marked` with a pass that repeats until no mark changes. The plugin and the shell need no change. The fixtures of 0189 gain more cases. A contract calls a member whose contract calls a plain member function. A member calls a plain member function whose contract has no model. A call stands on a local, on the right of `||` and in a loop condition. A member function calls a virtual function of an interface. The core test of 0189 checks the value of the call.
