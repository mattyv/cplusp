# 0147: A vector by reference that a call passes on is refused by name

Date: 2026-10-14. Status: decided. Amends 0145.

## Decision

- A call that passes a vector by reference to a parameter of type `std::vector<T>&` has no rule yet, decision 0145. The translator refuses it with the sentence `v is a vector by reference. A call that passes it on has no rule yet.` at the line of the call.
- A call that passes it to a parameter of type `const std::vector<T>&` reads the current value. It does not change.

## Why

The review of 0145 found that the refusal said `v is a parameter. The translator writes only a local or a reference parameter.` But `v` is a reference parameter, so the sentence was false. A bot that reads it cannot find the fix. The new sentence names the gap.
