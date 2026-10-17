# 0151: A 32-bit x86 target and an unknown attribute are refused

Date: 2026-10-17. Status: decided. Amends 0021, 0032 and 0128. The review of step two of doubles found both gaps.

## Decision

- The gate refuses a target of 32-bit x86, under the floating-point fault of 0128. These are `--target=X`, and `-target X` or `-arch X` where `X` is the next flag. `X` is refused when it starts with `i386`, `i486`, `i586` or `i686`. `-m16` is refused too.
- The row `unlisted` names the compiler warning `unknown-attributes`. So an attribute that clang does not know is a finding, such as `[[gnu::optimize("fast-math")]]` or `__attribute__((optimize("-ffast-math")))`.

## Why

On 32-bit x86, clang computes a `double` with the x87 unit, and `__FLT_EVAL_METHOD__` is 2. So `a + b` keeps 80 bits, and the model of one rounding to binary64 per operation is false. `-m32` was refused already, but a target triple gave the same build. Step one of doubles only compares, and a comparison is exact either way. Step two rounds, so the gap must close first.

Clang drops an attribute that it does not know, with a warning, before the allowlist of attributes can see it. GCC reads `optimize`, and fast math changes the results of floating point. So a team that builds with GCC got fast math in a function that the gate passed.
