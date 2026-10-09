# 0084: true and false in a contract, and the words of an error in the companion file

Date: 2026-10-09. Status: decided. Amends 0064 on the contract language and 0083 on the words of `prove`.

## Decision

- A contract reads `true` and `false` as the two values of `bool`. Before, a contract read each of them as a name, and refused it as no parameter.
- Each error that Dafny reports on a line of the companion file prints as `Dafny says:` and the message of Dafny. The sentences of 0068 speak of a return, a call and a loop of a method. A function of the companion file has none of these, so those words would send the author to the wrong place.

## Why

The sweep of the examples found contracts with `true` and `false`. The third review of the companion check found an error in a companion function. `prove` named it as an ensures line that may not hold on a return.
