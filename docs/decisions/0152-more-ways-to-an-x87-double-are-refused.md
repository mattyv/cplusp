# 0152: More ways to an x87 double are refused

Date: 2026-10-17. Status: decided. Amends 0151.

## Decision

- A 32-bit x86 target is a name that starts with `i`, one digit from `3` to `9`, then `86`. So `i786`, `i886` and `i986` are refused with the four of 0151.
- The gate refuses `-mno-sse`, `-mno-sse2` and `-mgeneral-regs-only`, under the floating-point fault of 0128.
- The row `unlisted` also names the compiler warning `ignored-attributes`.

## Why

The review of 0151 found three more ways to a build where a `double` uses the x87 unit. LLVM reads `i786` to `i986` as 32-bit x86, and clang gives `__FLT_EVAL_METHOD__` 2 for them. On the default x86_64 target, `-mno-sse` and `-mno-sse2` make clang and GCC compute `a + b` with `faddl`. Clang drops `__attribute__((target("fpmath=387")))` with the warning `ignored-attributes`, and GCC obeys it. `-msoft-float` and `-mx32` keep `__FLT_EVAL_METHOD__` at 0, so they stay.
