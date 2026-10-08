# 0062: A loop contract reads the variables in scope, and a contract line after code belongs to nothing

Date: 2026-10-08. Status: decided. Amends 0061 on the names of a loop contract, and 0057 on which lines a function claims.

## Decision

- A loop contract reads the parameters and the locals that are in scope at the loop. A local in the start of a `for` is in scope for its contract. A local declared inside the loop, or after it, is no variable of the contract, and the core refuses the name.
- A `//@` line after code on the same line belongs to no function and no loop. The plugin refuses it as a line that belongs to no function.
- The lines that a loop claims stop at the start of the body of its function. So a loop on the line of the function's name leaves the function its contract lines.

## Why

The review of slice 3 found three faults. A `//@ ensures` after the signature on the same line was neither claimed nor refused, so a false contract was dropped and the gate passed. A loop on the line of its function took the function's contract lines, and refused them as lines in the wrong place. With the flat list of 0061, a name that is out of scope made Dafny refuse the whole file and hide every other result.

## What changes

The core carries the variables in scope through the statements, in the order of the source, in place of the flat list. The plugin scans every line that holds `//@` for orphans, and it gives the loop's walk upward a floor at the start of the function's body.
