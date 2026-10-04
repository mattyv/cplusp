# 0024: Verified code is `double` only

Date: 2026-10-04. Status: decided. Extends 0019, 0020 and 0023.

## Decision

Verified code uses `double` and no other floating-point type. The gate refuses `float` and `long double` under the row `double_only`. Trusted code may hold a `float` that comes from outside, and converts it to `double` at the edge. The model file is named after its type, `Double.dfy`.

## Why

The model is of IEEE 754 binary64. Its unit round-off, its smallest subnormal and its largest value are the ones of `double`. A `float` has a unit round-off of 2^-24, about a billion times the one of `double`. A proof of float code against the double model would hold for a bound the hardware does not keep. The battery case `single_precision` shows it: a float sum of 1 and 1e-8 is 1, and the double bound allows about 1e-16. Nobody has asked for 32-bit arithmetic in verified code. When somebody does, a second model with the binary32 constants is the upgrade path.

## What changes

The row `double_only` with its sample pair. The battery case `single_precision`. The file `Float.dfy` is renamed `Double.dfy`, and its module is `Double`.
