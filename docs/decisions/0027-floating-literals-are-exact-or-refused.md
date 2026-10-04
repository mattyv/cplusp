# 0027: A floating-point literal is exactly a double, or the gate refuses it

Date: 2026-10-04. Status: decided. Extends 0024.

## Decision

Verified code writes only floating-point literals that are exactly a double. A hex float always is. A decimal is when a double holds its value, such as `0.5`, `1e3` or the exact expansion of a double. The gate refuses every other literal under the row `inexact_literal`. Its check asks the compiler's own float library whether the spelling converts without loss. For a tenth, the code divides by `10.0`.

## Why

The model reads a literal as the real it spells, and `0.1` is not a double. The compiler rounds it before the first operation, so `a * 0.1` rounds twice where the contract counts once. The battery case `double_literal` shows it. `tenth(3.0)` misses the real 0.3 by more than the one-rounding bound, under clang and GCC. The naive model proves the bound. The other way out, a model that rounds every literal, needs a proof about a product of two rounded values. That is nonlinear arithmetic the prover handles badly, and a bound the bot cannot write. Refusing the literal keeps the one-rounding rule true as it stands.

## What changes

The row `inexact_literal`, its sample pair and the plugin check `cplusp-inexact-literal`. The battery case `double_literal`. The skill tells the bot to divide by an exact literal.
