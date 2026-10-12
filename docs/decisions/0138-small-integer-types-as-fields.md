# 0138: int8_t, int16_t and uint16_t can be fields of a struct

Date: 2026-10-12. Status: decided. Amends 0106.

## Decision

- A field of a plain struct can have the type `int8_t`, `int16_t` or `uint16_t`. The field has the Dafny newtype of decision 0106, so Dafny proves that each value that the code puts in the field fits.
- These types are still no element of a sequence and no value of an optional. The type of an element or of a value is a scalar of the core, and the scalars do not hold them.

## Why

The survey of the examples that do not prove found that `message_header` stops at a `uint16_t` field of `Header`. With the field in, and decision 0137, the example proves. Decision 0106 gave no reason to keep these types out of a field. The plugin left them out because they are no element and no value of an optional. A field in the core has the full type of the subset, so it needs no scalar.
