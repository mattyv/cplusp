# 0104: A call inside an expression

Date: 2026-10-09. Status: decided. Amends 0058, where a call stands alone.

## Decision

- A call inside an expression of code runs before its statement, when C++ evaluates it once each time the statement runs. Its value goes to a temporary, and the expression reads the temporary. Its arguments can hold calls too, as in `f(g(x))`, and the inner call runs first.
- The calls run in the order that the source names them. C++ does not fix the order of the operands of most operators. The order does not change the value, because a call in an expression changes nothing but its value. A call of a function that writes its object stays refused in an expression, decision 0096.
- A call that C++ may not evaluate, or evaluates again, has no rule yet, and the translator refuses it at its line. That is a call on the right of `&&` or `||`, or in a branch of `?:`. It is also a call in the condition of a `while` or a `for` loop.
- Each call keeps its contract. The prover proves the requires lines of the callee where the call runs, and it uses the ensures lines for the value of the temporary.
- The sentence of the refusal says where a call can stand: `a call out of place. The translator takes a call where it always runs once, and a call that writes its object or gives no value only alone.`

## Why

The examples call functions inside expressions, as in `return m[index(i, j, cols)];` and `return low_bits(w) + 1;`. Five examples stopped at such a call. The rule of 0058 kept each call alone, so that a Dafny expression holds no call. A temporary for each call keeps that property, since the Dafny expression reads the temporary.
