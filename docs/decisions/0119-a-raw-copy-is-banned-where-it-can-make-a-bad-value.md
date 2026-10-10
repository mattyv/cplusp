# 0119: A raw copy is banned where it can make a value that is not one

Date: 2026-10-10. Status: decided. Amends 0118.

## Decision

The row `type_punning` bans each raw copy of bytes that can make a value its type does not have. The row holds in trusted code too. A raw copy is a bit cast, a `memcpy`, a `memmove` or a `memset`. A write through a pointer or a reference to bytes that is not const is one too. The row bans it in each of these cases.

- The type that the copy writes holds a pointer, a reference, an enum or a `bool`, at any depth. A pointer or a reference makes a pun. An enum or a `bool` can get a bit pattern that is no value of its type.
- The type that the copy reads has padding, and the type that it writes is not bytes. The padding has no value, [bit.cast] paragraph 2.
- The gate cannot know the type, because the copy goes through `void*`. The row fails closed there.

A copy into a type that holds only integers and floating types stays allowed when the source has no padding. Each bit pattern of such a type is a value. A read through a pointer to const bytes stays allowed. The `std::byte` of the system header holds no bad value. A `std::byte` that the file declares itself counts as an enum, decision 0117.

Two functions of the library make a bit cast like `std::bit_cast`. The row counts each one as `std::bit_cast`: `std::experimental::__bit_cast` and `std::experimental::__proposed::simd_bit_cast`.

## Why

The review of 0118 found a padded source, the library bit casts, and the cast to an array of `std::byte`. It also found that `memcpy` and a write through a byte pointer make the same bad values as a bit cast. The user chose to ban them in trusted code too, in the narrow form of 0118. So a copy of plain integer data stays legal, and the example `raw_memory_ops` keeps its trusted `memcpy` of two integers.
