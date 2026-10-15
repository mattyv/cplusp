# 0150: A double that only compares is a real, step one

Date: 2026-10-15. Status: decided. Amends 0019, 0020 and 0024 for the translator. The user chose this direction on 2026-10-13.

## Decision

- The translator models a `double` as a Dafny `real`, as 0019 says. Step one takes the forms that need no rounding. These are a parameter, a local, a result and an assignment, and a call that gives a `double`. Also the comparisons `<`, `<=`, `>` and `>=`, the prefix `-`, and `c ? a : b`.
- A finite double is a real, and a comparison of two finite doubles is the comparison of the reals. A prefix `-` is exact. So these forms keep the C++ value.
- A literal of type `double` has a rule when its value is `d / 10^k`, with `d` and `k` small enough for the core. Examples are `0.0`, `100.0` and `0.5`. Any other literal has no rule yet.
- In a contract, a decimal literal such as `150.0` is that real, and `std::isfinite(x)` reads a double. The model has no NaN and no infinity, so it is `true` there.
- Because the model holds no NaN and no infinity, the translator needs the words that keep them out. Each `double` parameter of a function needs `std::isfinite(x)` as a part of a requires line, joined by `&&`. A trusted function that gives a `double` needs `std::isfinite(result)` as a part of an ensures line. A verified function that gives a `double` needs nothing, because each value that it gives is finite.
- The core refuses each step that rounds. These are `+`, `-`, `*` and `/` on a double, `+=` and its family, and `++` and `--`. The sentence is `a double operation rounds, and the translator has no rule for it yet.` Step two adds them with the rounding axiom of 0023.
- A conversion between an integer and a double has no rule yet. Nor has a field of type `double`, or a sequence, an optional, a pointer or a reference of `double`.

## Why

The user chose doubles as the third block. The example `double_only` compares and returns, so it needs no rounding. A step without rounding adds no axiom, so it is the safe first step. The core refuses each rounding operation. So the model can never make exact real arithmetic out of a C++ operation that rounds.
