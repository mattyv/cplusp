# 0117: More forms of a pun, and what stays open

Date: 2026-10-10. Status: decided. Amends 0116.

## Decision

The review of the row `type_punning` found five forms that made a pun and passed the gate. The row now bans each one, in all code.

- A cast from an integer to a pointer. A round trip of a pointer through an integer makes the same pointer as a cast.
- `std::bit_cast` with a result of a class type, or with an argument that is a pointer, a class or an array. A class can hold a pointer, such as a `std::span`, so a bit cast to it makes the same pun. This also closes the bit cast to a struct that holds an enum, which decision 0115 left open.
- `std::reinterpret_pointer_cast` and `std::static_pointer_cast`. They cast inside a header of the system paths, where the gate judges no cast.
- A cast to a pointer to a function of another type. A call through it has no meaning in C++, [expr.call]. Decision 0116 made no exception for functions, and the green step must not add one.
- A `std::byte` that the file declares itself. Only the `std::byte` of the system header is a view as bytes.

Two forms of undefined behaviour stay open, and docs/soundness.md records them. A pointer to a member of another class can read a member that is not there, [expr.mptr.oper]. Placement new of another type over an object ends its life, so a read of the old object has no meaning. Each needs a decision of its own.

## Why

The user asked to ban each form of undefined behaviour. Decision 0116 claimed that the row banned each cast that makes a pun, and the review showed five that it did not. docs/soundness.md said the same, and it was false until this decision.
