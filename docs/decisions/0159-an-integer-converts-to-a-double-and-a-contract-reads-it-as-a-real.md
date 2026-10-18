# 0159: An integer converts to a double, and a contract reads an integer next to a real as a real

Date: 2026-10-18. Status: decided. Amends 0154 and 0158. The user asked for the rest of the doubles before the vectors on 2026-10-18.

## Decision

- In code, a conversion of an integer to a double is `fint(n)` of `Double.dfy`. It holds for an implicit conversion and for `static_cast<double>`. `fint` requires that `n` is at most 2^53 in magnitude, and it ensures that the result is `n` as a real. Its body calls the axiom `RoundExactInt`, which `Double.dfy` already has, decision 0023. So the model holds no new axiom.
- Dafny proves the requirement of `fint` at each conversion, from the contract and the type. An integer of 32 bits or fewer always meets it. A failure has the sentence `the integer may be too large for an exact double.`
- When the model calls `fint`, `prove` prints a line for its axiom before its verdict. The line is `Axiom: Double.dfy: RoundExactInt: an integer up to 2^53 in magnitude is a double.` The line of 0154 stays for the four operations.
- A conversion of a double to an integer, or of a bool to a double, stays refused.
- In a contract, `|e|` of an integer is the absolute value of the integer, `trunc_size(e)` of the prelude. `|e|` of a real stays `abs(e)`.
- In a contract, an integer name, field or `result` next to a real is that integer as a real, as a literal is in 0158. The conversion is exact, because a contract reads an integer as its exact value. An operation on integers alone, such as `n / 2`, stays an integer next to a real. Dafny refuses the line for its types, as in 0158.

## Why

The example `fixed_point` converts a count of thousandths to a double for a display. Its contract reads `f.raw / 1000.0` and `|a.raw * b.raw|`. The model of 0153 calls the operation and nothing else, so the conversion is one more function of that form. An integer above 2^53 in magnitude rounds. The model has no rule for that yet, so it requires the bound, and Dafny names a call that may not meet it.

An integer operation keeps the meaning of 0088 next to a real, so `n / 2` truncates first. A reader can misread that, so the translator refuses it and does not choose a meaning.
