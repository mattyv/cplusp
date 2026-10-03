---
name: cplusp-dafny
description: Rules for writing the Dafny model of a C+P function by hand, one rule per known divergence between C++ and Dafny. Use when writing or reviewing Dafny for cplusp.
---

# Writing Dafny for C+P

A case in `divergence/dafny/cases/` found every rule here. The case shows the naive model, the divergence, and the mitigation. Follow the rules. When a construct has no rule, stop and write the case first.

## signed_overflow

Map `int32_t` to `newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000`, never to `int`.
Dafny then checks every arithmetic step for overflow, in the body and in the contract alike.
A sum that may overflow needs a precondition written with `as int`:
`requires -0x8000_0000 <= (a as int) + (b as int) < 0x8000_0000`.
The other mitigation is in the C++: add in `int64_t` and check the range before narrowing.

## unsigned_wrap

Map `uint32_t` to `newtype uint32 = x: int | 0 <= x < 0x1_0000_0000`.
Unsigned arithmetic wraps in C++ and does not wrap in Dafny.
Where the C++ means to wrap, write `wrap32((a as int) - (b as int))` with the helper `wrap32(x: int) = (x % 0x1_0000_0000) as uint32`.
Dafny `%` is never negative, so this is the C++ result.
Where the C++ does not mean to wrap, add a precondition such as `requires b <= a`.

## integral_promotion

C++ promotes types narrower than `int` to `int` before arithmetic.
Model the sum in `int32`: `(a as int32) + (b as int32)`.
Convert the result back with a wrap helper such as `wrap8(x: int) = (x % 0x100) as uint8`.
A conversion to an unsigned type wraps in C++, so the helper is exact.
For a signed target type, see `narrowing_cast`.

## signed_division

Dafny `/` and `%` round toward negative infinity, and C++ rounds toward zero.
Never carry `/` or `%` over on signed values.
Use `trunc_div(a, b)` and `trunc_rem(a, b)`, which divide the absolute values and then set the sign.
The contract must require `b != 0`.
It must also exclude `a == INT32_MIN && b == -1`, because the quotient does not fit.

## narrowing_cast

Dafny `x as int8` needs a proof that `x` fits in `int8`.
The model never wraps, although C++20 does.
Put the fit in the C++ contract: `requires -0x80 <= x < 0x80`.
If the C++ means to wrap, it must wrap in its own code and then cast a value that fits.

## shift

Dafny has shifts on bit-vector types only, so map `uint32_t` to `bv32` in code that shifts.
Dafny accepts a shift by the full width, but C++ does not.
Write `requires n < 32`, never `requires n <= 32`.
The same holds for right shifts and for every other width.

## sign_compare

Dafny will not compare an `int32` with a `uint64`, and `as int` on both sides gives the true comparison, not the C++ one.
C++ converts the signed operand to unsigned first, so a negative value compares as a huge value.
Do not model a mixed comparison as it stands.
Change the C++ to test the sign and cast on purpose, for example `i < 0 || static_cast<size_t>(i) < n`.
Model the changed C++ as `i < 0 || (i as uint64) < n`.
`std::cmp_less(i, n)` from `<utility>` is the same test, and its model is `(i as int) < (n as int)`.

## plain_int

Map only fixed-width types, such as `int32_t` to `int32` and `uint8_t` to `uint8`.
The compiler sets the width of plain `int`, `long`, `short` and `char`, and the source does not.
Do not guess a width for them.
Change the C++ to a fixed-width type, and then model that.
Map `size_t` to `uint64`, which assumes a 64-bit target.

## reference_aliasing

Never model a reference parameter as an in value and an out value.
Model it as an object, `class Ref { var v: int32 }`, with a `modifies` clause.
Dafny then proves the contract for the case where two references are the same object.
When the contract is false for that case, add `requires a != b` to the model and `requires &a != &b` to the C++ contract.
Callers must then prove that the two are different.

## evaluation_order

Dafny has no method call inside an expression, so the model must choose an order.
C++ does not choose one for arguments, and compilers differ.
Never model two calls that change state in one expression.
Change the C++ to put each call in its own statement.
Then hoist the calls in the same order.

## loop_underflow

Dafny refuses `n - 1` on an unsigned value when `n` may be 0.
Do not model code that relies on a wrap below zero.
Change the C++ to count down to zero without going below it: `for (size_t i = n; i > 0; --i)`, and use `i - 1` inside.
A test `i >= 0` on an unsigned counter is always true, and the loop never ends.
Give every loop an invariant and a `decreases` clause.

## index_out_of_range

Model an array or a vector as a `seq`, and its size as a fact about `|a|`.
Every subscript becomes `a[i]`, and Dafny asks for a proof that the index is in range.
Do not weaken the proof. Write `requires i < |a|` in the contract, so the caller carries the obligation.

## optional_deref

Model `std::optional<T>` as `datatype Option<T> = None | Some(value: T)`.
Model `*opt` as `opt.value`. Dafny then asks for a proof that `opt` is `Some`.
Write `requires opt.Some?` in the model and `requires opt.has_value()` in the C++ contract.

## bool_from_int

Dafny has no conversion from an integer to `bool`.
Where C++ converts an integer to `bool`, write `x != 0` in the model.
Every value other than 0 is true, including values other than 1.
