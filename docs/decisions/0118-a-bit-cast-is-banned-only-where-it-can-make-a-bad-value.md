# 0118: A bit cast is banned only where it can make a value that is not one

Date: 2026-10-10. Status: decided. Amends 0117.

## Decision

- Decision 0117 banned each `std::bit_cast` with a class result, or with an argument that is a pointer, a class or an array. That rule also banned a bit cast that C++ defines, such as a struct of two `int32_t` to a `std::array<int32_t, 2>`.
- The row `type_punning` now bans a `std::bit_cast` only when its result type holds a pointer, an enum or a `bool`, at any depth. The depth covers the type itself, a field, a base, and an element of an array. A pointer makes a pun. An enum or a `bool` can get a bit pattern that is no value of its type. For a `bool`, C++ gives that read no meaning, [bit.cast]. For an enum, the model holds only its enumerators, decision 0109.
- A bit cast between types that hold only integers and floating types stays allowed. Each bit pattern of such a type is a value.
- A bit cast from a pointer to an integer stays allowed, because it makes no pointer. Decision 0117 bans a cast from the integer back to a pointer.
- A matcher cannot look through the fields of a type, so the plugin does this with a check of its own.

## Why

The user chose this form over the broad rule. The broad rule refused a legal bit cast in a fixture of the test suite. The aim is to ban each form of undefined behaviour, not legal code.
