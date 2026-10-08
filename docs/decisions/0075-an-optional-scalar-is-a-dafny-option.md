# 0075: An optional scalar is a Dafny Option

Date: 2026-10-08. Status: decided. The third step of the fifth slice in 0072.

## Decision

- `std::optional<T>`, where `T` is a scalar of the subset, is the Dafny type `Option<T>`. The prelude declares `datatype Option<T> = None | Some(value: T)`, as the battery case `radix_find` does. A value of it is a value, as 0029 says, and a copy is the same value.
- An optional is in the subset as a parameter by value or by const reference. It is also in the subset as a local, as a result and as a field of a struct.
- In code, `o.has_value()` is `o.Some?`. Both `*o` and `o.value()` are `o.value`. Dafny proves at each read that the optional holds a value. C++ gives no value for `*o` on an empty optional, and `o.value()` throws. The model refuses both: code that reads an empty optional does not prove.
- In code, `std::nullopt` is `None`. The compiler can turn a value into an optional, as in `return x;` from a function that gives an optional. That optional is `Some(x)`. A copy of an optional to an optional of the same type keeps the value.
- In a contract, `o.has_value()` and `o.value()` read a parameter, `result` or a field. `o.value()` of an integer reads as an exact integer. Dafny proves that each contract line reads `o.value()` only where `o` holds a value. So a contract line guards the read, as in `result.has_value() ==> result.value() >= 0`.
- A write to an optional, `if (o)` and a comparison of an optional have no rule yet. Neither has an optional of a struct or of a sequence.

## Why

`radix_find` gives an optional, and its nodes hold one. An optional of a scalar needs no heap, so the value model of 0029 holds. The two reads of C++ fail in two ways on an empty optional. The model treats both as a fault, so it needs no rule for the throw.

## What changes

The core gains the optional type, the three forms in code, the construction from a value, and the two reads in contracts. The parser gains the tokens `.has_value()` and `.value()`. The plugin writes the type, the reads, `std::nullopt` and the construction. The shell prints the type and the prelude line. `cplusp prove` names a read of an optional that may be empty.
