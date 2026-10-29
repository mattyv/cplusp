# 0202: A variant of two types

Date: 2026-10-29. Status: decided. Builds on 0064, 0075 and 0079. The example `optional_expected_variant` reads a `std::variant<int32_t, bool>` parameter with `std::holds_alternative` and `std::get`, in code and in its contracts.

## Decision

A `std::variant<A, B>` is a type of the model when `A` and `B` are two different element types of 0064 or 0076, such as `int32_t`, `bool` or a plain struct. It can be a parameter by value or by `const&`. The prelude has the datatype `datatype Variant<A, B> = Alt0(alt0: A) | Alt1(alt1: B)`. A variant that holds an `A` is `Alt0`, and one that holds a `B` is `Alt1`.

- `std::holds_alternative<T>(v)` is `v.Alt0?` when `T` is `A`, and `v.Alt1?` when `T` is `B`.
- `std::get<T>(v)` is `v.alt0` when `T` is `A`, and `v.alt1` when `T` is `B`. Dafny checks that `v` holds that alternative, in code and in a contract. In code, this check shows that `std::get` never throws `std::bad_variant_access`.

When the check fails, `prove` gives the sentence `the variant may not hold this alternative.`

The two forms have the same meaning in code and in a contract. In a contract, `T` is a type name of 0064, such as `int32_t` or `bool`. A contract cannot name a struct as `T` yet. A contract that names a type that is not `A` or `B` gets the sentence `the contract line has a form the translator cannot read.`

The rest has no rule yet. The translator refuses each of these at its line, with the sentence of its kind.

- A variant with more than two alternatives, or with two alternatives of one type.
- A variant as a local, a result, a field or a reference that is not `const`.
- `std::get<I>(v)` by index, `std::get_if`, `std::visit`, `v.index()` and an assignment to a variant.

## Why

A variant says in its type which values it can hold, and the read of the wrong alternative throws. So the proof must show that each `std::get` reads the alternative that the variant holds. A datatype with one constructor for each alternative gives that check for free, because Dafny checks each read of a destructor. Two alternatives cover the example and the common case of a value or an error. The ceiling is two alternatives. The upgrade path is a datatype for each arity.

## What changes

The core gets the type of a variant and the two reads, in code and in a contract. It also gets the two tokens of the contract language and the datatype in the prelude. The plugin gives the type of a variant parameter, and the two reads as calls of the two functions of the standard library. The shell prints the type. Three fixtures follow the form of 0178.
