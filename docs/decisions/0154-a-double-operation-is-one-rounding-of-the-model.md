# 0154: A double operation is one rounding of the model, step two

Date: 2026-10-17. Status: decided. Amends 0150. The review of step two gave the go on 2026-10-17, with the conditions of 0151 to 0153.

## Decision

- In code, `a + b`, `a - b`, `a * b` and `a / b` on doubles are `fadd(a, b)`, `fsub(a, b)`, `fmul(a, b)` and `fdiv(a, b)` of `Double.dfy`, decision 0153. So `x += e` and its family are the same. Each call requires that the exact result is at most `DBL_MAX` in magnitude. `fdiv` also requires a divisor that is not zero. Dafny proves these at each operation, from the contract.
- `++`, `--` and `%` on a double stay refused, with the sentence of 0150.
- In a contract, `|e|` is the absolute value of a real. `eps` is 2^-53, `eta` is 2^-1075 and `DBL_MAX` is the largest double, as in 0020 and 0023. These three are words of the contract, so a parameter with one of these names cannot be read in a contract.
- The model holds the module `Double` from `divergence/dafny/Double.dfy` when it calls one of the operations. The shell takes the text of that file as it is, and keeps no copy.
- When the model calls one of the operations, `prove` prints one line before its verdict. The line is `Axiom: Double.dfy: RoundError: IEEE 754 binary64, round to nearest even, gradual underflow, one rounding per operation.` The shell prints it, because the printer is the part that writes the calls. The line tells the reader what the proof assumes, and the verdict does not depend on it.
- A failed bound has its own sentence. A result that may pass `DBL_MAX` is `the result of the operation may exceed DBL_MAX.` A divisor that may be zero is `the divisor may be zero.`, as for integers.
- A companion file cannot declare a name of the module, such as `abs`, `round`, `fmul`, `EPS` or `Double`, decision 0083.
- These have no rule yet: a literal that is not `d / 10^k`, such as `0x1p-30`. Also a `constexpr` double, an integer next to a real in a contract, and a conversion between an integer and a double.

## Why

The review of step two found that the axiom is true of IEEE 754 binary64 and cannot prove false. It also found two gaps in the gate, which 0151 and 0152 close, and it chose the shape of 0153. With that shape, the translator writes only the call of the operation, and the model cannot forget the bound. The first slice covers `product` of the example `double` and the three other operations. The rest of that example, and `double_expression`, need forms of the last point.
