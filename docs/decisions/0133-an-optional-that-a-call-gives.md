# 0133: has_value, value and the star read the optional that a call gives

Date: 2026-10-12. Status: decided. Amends 0075.

## Decision

- In code, `f(x).has_value()`, `f(x).value()` and `*f(x)` are in the subset when `f` gives a `std::optional` of a scalar. The compiler holds the result of the call in a temporary, and the method reads the temporary. The model reads the value that the call gives. Dafny proves that the optional holds a value wherever the code reads it, as for a local, decision 0075.
- The plugin looks through the temporary only at these three reads. A temporary anywhere else stays unknown.
- The value is a scalar, so the read copies it out of the temporary. A reference that holds the element of a temporary has no rule. So the end of the temporary cannot leave a reference that points nowhere.

## Why

The survey of the examples that do not prove found that `binary_search` stops only at `binary_search(a, key).has_value()` in `contains`. A temporary that the compiler makes for a value gives the same value, and the model of 0029 is a model of values.
