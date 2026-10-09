# 0099: Assert and apply lines in a body

Date: 2026-10-09. Status: decided. Amends 0080 on what a companion file may hold, and 0062 on what a loop contract reads.

## Decision

- `//@ assert e` on its own line in a body states a fact at that place. Its Dafny form is `assert e;`. The prover proves the fact, and then it uses the fact for the rest of the proof.
- `//@ apply L(a, b)` calls the lemma `L` of the companion file at that place. Its Dafny form is `L(a, b);`. The prover proves the requires lines of the lemma, and then it uses the ensures lines.
- An assert or apply line stands directly above a statement of the same block, with only other `//@` lines or comments between them. It holds before that statement. A line below the last statement of its block has no statement to stand above, so the translator refuses it.
- The expression of an assert or apply line is a contract expression, decision 0060. It reads the variables in scope at its place, as a loop contract does, decision 0062. It names no `result`.
- A contract in a body reads the object of a member function as the body has it at that place. This is true for an assert line, an apply line and a loop contract. In a member function that writes its object, a field name reads `this'`, and `old(f)` reads the field before the call, decision 0096.
- A companion file may also hold a lemma with a body. A lemma with no body is an axiom, and the companion file is refused, as for a function with no body, decision 0080. `assert` may stand in the body of a lemma.

## Why

25 of the examples state steps that Dafny cannot find alone, in asserts and in calls of lemmas in their example.dfy. The example checksum needs two asserts in its loop, as its example.dfy shows. A lemma is a proved fact, so it adds no assumption. A lemma with no body would add one, so the check of 0080 refuses it.
