# 0141: A pointer has its own type in the core, and two pointers do not compare

Date: 2026-10-12. Status: decided. Amends 0140.

## Decision

- The core has a type for a pointer to const, `Ptr(T)`. Dafny still reads it as `Option<T>`, as decision 0140 says. The core keeps it apart from an optional, because a comparison means another thing for each.
- A comparison of two pointers has no rule, in code and in a contract. That covers `==`, `!=`, `<`, `<=`, `>` and `>=`. In C++ it compares two addresses, and the model has no addresses.
- `p == nullptr`, `p != nullptr` and `nullptr` on the left are the only comparisons of a pointer. In a contract, they need a pointer. The code tests an optional with `has_value()`, as before.
- `*p` and `p->f` read a pointer. `has_value()` and `value()` stay on an optional. In a contract, `*o` reads an optional too, decision 0131.
- `this == nullptr`, and any comparison of `this`, has no rule.

## Why

The review of 0140 found that `p == q` on two pointers to const proved as the equality of the two values. A caller passed `&x` and `&y`, with `x == y`, and proved `result == true`. In C++ the two addresses differ, and the result is false. The core read a contract `p == q` or `p < q` the same way. The core could not refuse it, because 0140 gave a pointer the type of an optional. In C++ a comparison of two optionals compares their values.

The review also found that `this == nullptr` reached Dafny and failed there with a message of Dafny.
