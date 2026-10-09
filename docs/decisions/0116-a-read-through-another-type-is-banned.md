# 0116: A read through a pointer or a reference of another type is banned

Date: 2026-10-09. Status: decided. Amends 0115.

## Decision

- A new gate row, `type_punning`, bans a cast that changes the type a pointer or a reference points to. This covers `reinterpret_cast`, a C cast, and `static_cast` from `void*`. The row holds in all code, trusted code too.
- A cast to a pointer or a reference to `char`, `unsigned char` or `std::byte` stays allowed. C++ lets any object be read as bytes. A cast to `void*` stays allowed, and so does a cast that only adds `const` or `volatile`.
- The row also bans a cast from `void*` to a pointer to an object type, also when the object has that type. The gate cannot know the type of the object, so a round trip through `void*` has no rule.
- The row also bans `std::bit_cast` to a pointer to an object type, because it makes the same pointer with no cast.
- C++ also lets an object be read as the signed or unsigned type of the same width. The row bans that too, for one simple rule. `std::bit_cast` gives the same value with no pointer.
- The row closes the pointer cast to a struct or an array that holds an enum, which decision 0115 left open in docs/soundness.md.

## Why

The user asked to ban each form of undefined behaviour. In C++, a read of an object through a glvalue of a type that the standard does not list has no meaning, [basic.lval] paragraph 11. The standard also gives no meaning to a member access through a pointer to a struct that is not there, [expr.ref] paragraph 10. Before this row, trusted code could do both. The review of the enum step found two programs that proved and were wrong because of it. No example and no trusted file of the repository needs such a cast.
