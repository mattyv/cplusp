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

## promotion_before_widening

C++ does arithmetic in the type of the operands, not in the type of the destination.
`a * b` on two `int32_t` is an `int32_t` product, and overflow in it gives undefined behaviour, even when the result goes into an `int64_t`.
When the result stays in `int32_t`, model the product in `int32` with the contract that it fits.
When the result widens, the gate refuses `a * b`. Widen an operand in the C++, `int64_t{a} * b`, and model the product in `int64`.

## implicit_narrowing

Dafny refuses an implicit narrowing, and so does the gate.
Cast on purpose, and put the fit in the C++ contract: `requires -0x80000000 <= x < 0x80000000`.
The model is then `x as int32`.
See `narrowing_cast`.

## compound_assign_narrow

A compound assignment on a type narrower than `int` computes in `int` and narrows on the store.
Write the narrowing as a cast: `a = static_cast<uint8_t>(a + 100)`.
Model it with the wrap helper: `wrap8(((a as int32) + 100) as int)`.

## signed_to_unsigned

The model refuses a signed value where the code needs an unsigned one, and so does the gate.
Put the sign in the contract, `requires i >= 0`, and cast on purpose.
The model is then `i as uint64`.

## unary_minus_min

`-x` has one value that does not fit.
The contract must exclude it: `requires x != -0x8000_0000`.

## abs_min

Model `std::abs` as `if x < 0 then -x else x`.
Exclude `INT32_MIN` in the contract: `requires x != -0x8000_0000`.

## increment_overflow

`++` and `--` are arithmetic.
They need the same contract as `+ 1` and `- 1`.
For `++x` write `requires x < 0x7FFF_FFFF`.

## signed_shift_left

Model a signed shift through `bv32`.
Convert a negative value by adding 2^32 first, and convert back by subtracting 2^32 when the top bit is 1.
State the postcondition on the bit pattern, `to_bv32(result) == to_bv32(x) << n`. Dafny proves the concrete values from it, not the general congruence.

## signed_shift_right

Dafny `/` rounds toward negative infinity when the divisor is positive, and `2^n` is positive.
Model a right shift as a division by a power of two.
Dafny `/` matches the C++ shift here. It never matches C++ `/` on negative values, see `signed_division`.

## literal_shift

A literal has its own type, and a shift takes the type of its left operand.
`1 << n` is a shift in `int`, whatever the type of the destination.
Write the literal in the destination type: `int64_t{1} << n`.

## bool_arith

C++ promotes `bool` to `int` in arithmetic.
Dafny does not.
Write `if b then 1 else 0`.

## enum_cast

Model an `enum class` as a datatype of its enumerators.
A cast from an integer needs a `requires` that the value is an enumerator, in the C++ contract and in the model.

## size_minus_one

`size()` returns an unsigned value.
`size() - 1` on an empty container is the largest `size_t`, and it is no error.
The contract must require a non-empty container, or the C++ must test `empty()` first.

## value_semantics

A C++ value is a Dafny `datatype`.
Model a struct or class held by value as a datatype, and a copy as the same value.
A field update is `p.(x := 5)`, a new value.
Use a Dafny `class` only for what the C++ reaches through a reference or pointer.

## object_lifetime

Dafny objects live for ever, and C++ objects die.
A pointer in verified code is a parameter only, never a member or a local.
So it cannot be stored past its object.

## reference_into_container

A `seq` element is a value, and a C++ reference into a container dies at the next mutation.
Copy the element out.
Never hold a reference into a container.

## member_init_order

C++ initializes members in declaration order, whatever order the constructor writes them in.
Write the mem-initializers in declaration order, and model the constructor in that order.

## slicing

A Dafny object never loses its class, and a C++ copy into a base type does.
Never copy a derived object into a base by value.
Bind a reference.

## virtual_in_constructor

A virtual call inside a constructor or destructor dispatches to the class under construction.
Dafny dispatches to the class of the object.
Do not call a virtual function from a constructor or destructor.

## virtual_destructor

Dafny has no destructor, so the model cannot see a wrong one.
Every class with a virtual function has a virtual destructor.
The gate enforces it.

## use_after_move

A moved-from value is unspecified, and Dafny has no move.
Never read a variable after `std::move` of it.
Model the move as a copy and the source as gone.

## moved_from_unique_ptr

A moved-from `unique_ptr` is null.
Model `unique_ptr<T>` as a nullable reference, and a move as the source becoming null.
Never read the source after the move.

## null_pointer

Model a pointer parameter as a nullable reference `T?`.
Dafny then asks for `p != null` at every read.
Put it in the contract.

## operator_meaning

An overloaded operator is a function.
Model `a + b` on a class type as a call to that function with its own contract, never as the built-in operator.

## generic_per_type

A template has no model.
Each instantiation is a function with its own types, and gets its own model.
The gate reads inside instantiations too.

## stack_depth

Dafny proves that a recursion ends, not that the stack holds it.
Bound the depth in the contract.
The bound is an assumption about the target, and docs/soundness.md gap 1 records it.

## constexpr_runtime

`constexpr` changes nothing in the model.
The compiler checks only the calls it evaluates at compile time.
A run-time call has the same contract as any function.

## interface_dispatch

A pure interface is a Dafny trait with the same functions.
A class that implements several interfaces extends several traits.
Dispatch through any of them is the same call.

## array_index

Model `std::array<T, N>` as a `seq<T>` with `|a| == N`.
Every subscript needs `requires i < N` in the contract, as for a plain array.

## span_dangling

A span is a pointer and a length, and Dafny has only values.
A span is a parameter only, never stored.
The gate enforces it.

## range_for_mutation

A Dafny loop over a `seq` reads a value.
A C++ range-for holds iterators into the live container.
The loop body never changes the range.
The gate refuses a direct call on the range, and a call that passes the range by non-const reference.

## count_if_lambda

A lambda passed to a std algorithm with by-value captures and no `mutable` is a pure function of its arguments and its captures.
Model the algorithm and the lambda together as one function over the `seq`.

## fold_init_type

A fold runs in the type of its init value.
Write the init value in the element type, or a wider one.
The gate enforces it.

## sort_contract

Model a std algorithm with a trusted contract as a bodyless `{:axiom}` method with that contract, and call it from the model of your function.
Never mark the model of your own function `{:axiom}`.
The trusted algorithms so far are `std::sort`, an axiom method with its contract in this skill, and `std::count_if`, modelled as a function over the `seq`.
`std::sort` gives a sorted permutation.
The comparator must be a strict weak order, and the default one on integers is.

## map_subscript

`m[k]` on a map writes.
Never model it as a read.
Use `contains` and `at`, which the gate allows, and model them as `k in m` and `m[k]`.

## string_npos

`std::string::find` returns `npos` for no match, and arithmetic on it wraps.
Model `find` as `Option<nat>`.
Test for `npos` before you use the result.

## switch_fallthrough

A `switch` falls through to the next case without a break, and a Dafny `match` never does.
No case runs into the next without `[[fallthrough]]`, and the gate enforces it.
Model a marked fall-through as one arm with both bodies.

## switch_missing_case

A Dafny `match` must cover every value, and a C++ `switch` need not.
Write a case for every enumerator, or a default.
The gate enforces it.

## optional_compare

A comparison of an optional with a value has a result when the optional is empty.
An empty optional is less than every value and equal to none.
Write the empty case out: `o.None? ||` for `<`, `<=` and `!=`, and `o.Some? &&` for `==`, `>` and `>=`.

## variant_get

Model `std::variant` as a datatype with one constructor per alternative.
A read of an alternative needs `requires` that the variant holds it, in the C++ contract and in the model.

## float_sum

A double is a real after rounding.
Model `a + b` as `fadd(a, b)`, and state the result as a bound, `abs(result - (a + b)) <= EPS * abs(a + b) + ETA`.
Never state equality of two float results.
The bound holds up to `MAX`, so require `abs(a) <= MAX / 4.0` and `abs(b) <= MAX / 4.0`.
Dafny does not apply a lemma by itself, so call `RoundError(a + b)` in the body before `fadd`.
In the C++ contract, write the bound as `|result - (a + b)| <= eps * |a + b| + eta`, with `eps` as `DBL_EPSILON / 2` and `eta` as `DBL_TRUE_MIN / 2`, and the magnitude bound `|a| <= DBL_MAX / 4` as a `requires`.
The model is `divergence/dafny/Double.dfy`. Write `include "Double.dfy"` with the path to it, and `import opened Double`.

## float_nan

The model has no NaN and no infinity.
Every float parameter requires `std::isfinite` in the C++ contract.
Never compare floats with `==`. The gate refuses it.
Compare against a tolerance `T` that is a double, and give the contract slack for the rounding of the difference.
`result` implies `|a - b| <= T + 2 * eps * T + 2 * eta`, and `|a - b| <= T - 2 * eps * T - 2 * eta` implies `result`.
Model the difference as `fsub(a, b)` with its `RoundError` call, never as the exact difference.

## float_to_int

Model `static_cast<int32_t>(x)` as truncation toward zero, not `Floor`.
Write `trunc(x)` as `if x >= 0.0 then x.Floor else -((-x).Floor)`.
The contract requires the value to fit: `requires -2147483649.0 < x < 2147483648.0`.

## float_cancellation

Every operation rounds, and the errors add.
State the bound from the magnitudes of the operands, not from the result the mathematics would give.
Call `RoundError` once for each operation, on the exact value that the operation rounds.
Each rounding adds `eta`, so a chain of roundings carries a small multiple of `eta` in its bound.

## float_increment

A bound of `EPS * abs(x)` is 1.0 at 2^53, so above it the model promises nothing about the last digit.
When the C++ needs exact counting, use an integer type.

## float_division_zero

The model has no infinity, and C++ calls float division by zero undefined.
The contract requires a non-zero divisor: `requires b != 0.0`.
The quotient must stay below `MAX`, so the model needs `requires abs(a / b) <= MAX`, and the C++ contract carries `|a / b| <= DBL_MAX`.

## int_to_float

An integer converts to a double exactly up to 2^53 in magnitude.
The contract requires that range, and `RoundExactInt` proves the equality.
Model the conversion as `round(n as real)`.

## pointer_into_container

A pointer parameter and a container cannot alias in the model, and in C++ a pointer into the container dies at the next mutation.
Never take the address of a container element.
The gate refuses it.

## float_underflow

A product or quotient can fall below the smallest subnormal and round to 0.
The `eta` term of the bound is what allows it.
State `|a * b| <= DBL_MAX` in the C++ contract, and never a lower bound.

## single_precision

The model is of `double` and of no other type.
Never write `float` or `long double` in verified code. The gate refuses them.
A `float` from outside is converted to `double` in trusted code at the edge, and the contract there is about the `double`.

## unlisted_modifies

A global is a field of one state object.
Every function that changes it lists it in `modifies`.
A trusted contract that omits it is false.
The gate check `cplusp-unlisted-state` does not exist yet, so the gate passes a function that changes a global without listing it.
Until the check exists, a reviewer must read the trusted contracts for this.

## static_local

A function-local static is a global with a narrow name.
Model it as a field of the state object, with `modifies` and `reads`.
Never model it as a local.

## global_constructors

A global with a dynamic initializer runs in an order the standard leaves open across files.
Model no such global.
Compute the value in a function, or make it `constexpr` or `constinit`.
The gate enforces it.

## torn_read

A variable another thread may change has no value, only a fresh read each time.
Model its getter as a method that does not constrain its result between calls.
The contract of the getter says only what every writer keeps, for example a range.
The getter is trusted code, and it must read an atomic. A plain read of a variable another thread writes is a data race.
Never prove two reads equal.
