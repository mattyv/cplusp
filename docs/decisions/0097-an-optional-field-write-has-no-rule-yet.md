# 0097: A write to an optional field has no rule yet

Date: 2026-10-09. Status: decided. Amends 0096, from the review of its green step.

## Decision

- In a member function that writes its object, `f = e` writes a field of a scalar type. A write to a field of an optional type has no rule yet, and the translator refuses it at its line.
- `return f();` of a `void` call has no rule. The translator refuses it at its line as `ReturnStmt`.
- A call alone as a statement stands when it writes its object or gives no value. Any other call alone is refused at its line, with a sentence that says where a call can stand.

## Why

The review found that 0096 promised a write to an optional field, and that no test held the promise. In C++ that write is a call of `operator=` of `std::optional`, so it needs its own rule: a value becomes `Some`, and `std::nullopt` becomes `None`. That rule comes in its own step with its own tests. The review also found that `return f();` and a dropped value got sentences that point at the wrong place.
