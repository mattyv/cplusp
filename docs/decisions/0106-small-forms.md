# 0106: Small forms: three integer types, a right shift, named constants and characters

Date: 2026-10-09. Status: decided. Amends 0029 on the integer types, and 0060 on what a contract can name.

## Decision

- `int8_t`, `int16_t` and `uint16_t` are integer types of the subset, as the others are, decision 0029. Each is a Dafny newtype of its range. A conversion to one of them is `(e as T)`, so Dafny proves that the value fits.
- `a >> n` is in the subset for an integer `a`. Its value is `a` divided by 2 to the power `n`, rounded down, as C++20 says for each integer type. The model is `shr(a, n, W)` of the prelude, where `W` is the width of the type of `a` after promotion. The function `shr` requires `0 <= n < W`, so Dafny proves the condition of C++ at each shift. Its ensures lines say that the result is between `a` and 0. `<<` still has no rule.
- A named constant of an integer type, declared `constexpr` at the scope of the file, reads as its value, in code and in contracts. A variable that is not `constexpr` is no constant, and a contract that names it is refused, as before.
- A character literal in a contract, such as `'0'`, reads as its code, an integer. In code, the compiler makes the same conversion.
- When Dafny cannot prove the condition of a shift, `prove` says `the shift amount may not be below the width of the type.` at the line of the shift.

## Why

Four examples stopped at one of these forms. Three proved when I patched the form out by hand: `narrowing_static_cast` at `int8_t`, `arithmetic` at `>>`, and `constexpr` at a named constant. The fourth, `parse_digits`, stops at `'0'` in a contract, and it also needs its companion file.
