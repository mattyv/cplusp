# 0101: A forall statement with no body is an axiom

Date: 2026-10-09. Status: decided. Amends 0099 and 0080, from the review of the green step of 0099.

## Decision

- A `forall` statement with no body states its ensures lines with no proof, as an `assume` does. In the body of a lemma of the companion file, it is an axiom. `cplusp prove` refuses it at its line, and it never says `proved` then. A `while` loop with no body counts the same, although a companion file cannot hold `while` today.
- An assert or apply line belongs to the block where it stands. Only a statement that starts its own line takes the `//@` lines above it. So the lines below the last statement of a block never move into an `else if` that follows.
- The refusal of a name that is not in scope at a contract in a body names the word of its line: `y in the assert line is no variable.`, or `z in the invariant line is no variable.`

## Why

The review found a lemma whose body held `forall y ensures Id(y) > y`, with no body. Dafny only warned, and the run said `ok: proved` for a wrong function. The review also found an assert line at the end of a then-block that moved into the `else if` below it. It proved there, although it was false at its place.
