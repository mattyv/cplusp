# 0120: The last forms of a raw copy, and the gap that stays open

Date: 2026-10-10. Status: decided. Amends 0119.

## Decision

The row `type_punning` also bans these forms of a raw copy, in all code.

- A pointer to bytes that is not const, made from an integer. The gate cannot know the object, so the row fails closed.
- A `const_cast` that takes const away from a pointer or a reference to bytes. The gate cannot know the object, so the row fails closed.
- `std::as_writable_bytes` of a span whose element holds a pointer, a reference, an enum or a `bool`.
- `bcopy`, `bzero`, `explicit_bzero`, `mempcpy` and `memccpy`, and each `__builtin_` name of a copy function. Each one is a raw copy, as `memcpy` is.
- The name of a copy function that is not called, for example in `auto copy = std::memcpy;`. The gate cannot follow the pointer, so the row fails closed at the name.
- A copy into a class with a virtual function or a virtual base. The class holds a hidden pointer.
- A copy into an incomplete type, or from an incomplete type into a type that is not bytes. The gate cannot know the fields, so the row fails closed.

The row now allows two cases that 0119 refused.

- A template with a type that depends on a parameter. The row judges each instance of the template, and not the template itself.
- An empty base and a field of size zero. They take no bits, so they are no padding.

An unnamed bit-field has no value, so it is padding. The row `bitfields` refuses each bit-field already, so this change shows nothing. The gate does not change for it.

Each finding of a raw copy tells the bot the reason. The sentence follows the message of the row. There are four sentences.

- `The copy writes a type that holds a pointer, a reference, an enum or a bool.`
- `The copy reads padding into a type that is not bytes.`
- `The copy writes to a place of unknown type.`
- `The copy reads a place of unknown type into a type that is not bytes.`

These forms stay open. A reviewer of the trusted body checks them, and docs/soundness.md lists them.

- A function of a library that writes bytes through a `void*` parameter, for example `fread`, `read`, `recv` or `getrandom`.
- Two allowed copies in a row: padding into bytes, then the bytes into integers. To find it, the gate must follow the data.
- Placement new of another type over an object, as in 0119.

## Why

The review of 0119 found seven more forms of a raw copy and three false refusals. The list of forms of a raw copy has no end. The user chose one last round: close the forms that one check can find, and write down the rest. The gate checks the code as written, and a human reviews each trusted body. So the remaining forms go to that reviewer.
