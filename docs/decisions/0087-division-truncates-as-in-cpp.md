# 0087: Division truncates as in C++

Date: 2026-10-09. Status: decided. Follows the rule of the battery case `signed_division`.

## Decision

- The prelude declares `trunc_div(a, b)` and `trunc_rem(a, b)` on exact integers. Each requires `b != 0`. `trunc_div` divides the sizes of `a` and `b` and then sets the sign, so it rounds toward zero, as C++ does. `trunc_rem` is `a - b * trunc_div(a, b)`, so its sign is the sign of `a`, as in C++.
- In code, `a / b` on an integer type `T` is `(trunc_div(a as int, b as int) as T)`, and `a % b` is the same with `trunc_rem`. Dafny proves that `b` is not zero, and that the quotient fits `T`. So `INT32_MIN / -1` does not prove. C++ gives undefined behaviour for both.
- In a contract, `/` and `%` are `trunc_div` and `trunc_rem` on the exact integers. Dafny proves that the divisor is not zero where the contract reads it.
- Dafny's own `/` and `%` never appear in the model. They round so that the remainder is never negative, which differs from C++ for a negative operand.
- The companion file may not declare `trunc_div` or `trunc_rem`, as for the other names of the model, decision 0083.

## Why

The examples `checksum` and `bitfields` use `%`, and `arithmetic` uses `/`. The model was checked by hand in Dafny: `trunc_div(-7, 2) == -3`, `trunc_rem(-7, 2) == -1` and `trunc_rem(7, -2) == 1`, as in C++. A division of `int32_t` with no bound on its operands does not prove, because `INT32_MIN / -1` does not fit.
