# 0175: Types that are an integer or a fixed sequence in the model

Date: 2026-10-23. Status: decided. Builds on 0058, 0109, 0114, 0132 and 0150. This is slice two of the plan of 0173, for the examples `bit_flags`, `enum_table`, `chrono`, `operator_overloading` and `reinterpret_const_cast`.

## Decision

An `enum class` with a fixed underlying type and a value written for an enumerator is its underlying integer. `Flag : uint32_t` is `uint32`. An enumerator is its value: `Flag::Read` is `1`. A value of the type is any value of the integer, as C++ has it. `static_cast` between the enum and an integer is the integral cast of decision 0058. The gate lets such a cast through, decision 0114. The model has every value, so it needs no enumerator for the cast. An `enum class` with no value written stays a datatype, decision 0109.

The bit operators `&` and `|` on unsigned integers are the functions `BitAnd` and `BitOr` of the prelude. Each is a recursive function on the bits, with no axiom. The prelude proves their laws as lemmas. A result of `BitAnd` is at most each operand. A result of `BitOr` of two values below `2^32` is below `2^32`. The laws of absorption and of a subset of bits hold. One lemma, `Laws`, gives all of them as quantified facts. Each method of a file that uses a bit operator calls `Laws()` as its first statement. In a contract, `a & b` and `a | b` are the same functions. A `|` between two values is `BitOr`. A `|e|` with no value before it stays the absolute value of decision 0154. A bit operator on a signed integer has no rule. The sentence is "a bit operator on a signed integer: the translator has no rule for it yet."

A free operator such as `operator+` or `operator|` is a function. Its Dafny name is `c_op'plus`, `c_op'minus`, `c_op'times`, `c_op'div`, `c_op'mod`, `c_op'bitand`, `c_op'bitor`, `c_op'eq`, `c_op'ne`, `c_op'lt`, `c_op'le`, `c_op'gt` or `c_op'ge`. A use of the operator on operands of a struct or of such an enum is a call of that function. An operator that is a member function keeps the sentence of today.

`std::chrono::milliseconds` is its count, an `int64`. `a.count()` is `a`, in code and in a contract. `a + b` of two values is the checked sum of the counts. `std::chrono::milliseconds{n}` is `n`. Any other duration has no rule yet.

`std::array<T, N>` by value is a read-only sequence of the fixed extent `N`, as the const form is in decision 0132. As a result it gives `|result| == N`. `return {a, b, c};` of such a result is the sequence `[a, b, c]`. A list with another number of values than `N` has no rule.

A parameter `const T&` of a scalar `T` is the scalar by value. The gate refuses a call that passes one object under two names, row `aliasing`, so the value is the same for the whole call.

A contract can write `static_cast<T>(e)` when `e` is a parameter, a field path, `result` or an enumerator, and each value of the type of `e` fits `T`. The cast is then the value of `e`. Any other cast in a contract has no rule. The sentence is "a static_cast in a contract that can change the value: the translator has no rule for it yet."

## Why

Five examples stop at a type whose values are the values of an integer. An enum with a value written is a set of bit patterns, and only the integer models it. Decision 0109 said so and left the model open. A `bv32` model times out in Dafny on the laws of two bits, in a hand check. A recursive function on the bits with proved lemmas verifies the example in three seconds. It needs no axiom. A duration and a const reference to a scalar are one integer each. A `std::array` by value is a copy that no one else can see, so the rule of decision 0132 holds for it.

## What changes

The plugin writes a valued enum as its integer. It writes an enumerator as a literal in code and as a constant for the contracts. It writes a free operator as a function with its readable name, and a use of it as a call. It writes a duration as `int64` and `.count()` as its object. It writes a `std::array` by value as a sequence, and a `const T&` of a scalar as the scalar. The core gains `BitAnd` and `BitOr` as operators, a sequence literal, the cast rule and the `.count()` rule for contracts. The shell prints the Bits prelude when a file uses a bit operator, with `Laws()` at the top of each method. Three fixtures: `model-int-types.cpp` proves, `model-int-types-wrong.cpp` fails at the named lines, `model-int-types-refuse.cpp` refuses with the sentences. The examples `enum_table`, `chrono`, `operator_overloading` and `reinterpret_const_cast` prove. `bit_flags` waits for decision 0176, because its contracts call `has`.
