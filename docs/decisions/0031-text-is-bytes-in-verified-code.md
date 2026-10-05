# 0031: Text is bytes in verified code

Date: 2026-10-05. Status: decided. Follows the hot-path round of examples.

## Decision

Verified code reads text as `std::span<const uint8_t>`. `std::string` and `std::string_view` are trusted only, under the row `strings`, and a search returns `std::optional<size_t>` rather than `npos`. The `throw` message points at a result struct with an error enum, and at `std::expected` once the toolchain compiles it. A larger example may carry a trusted body, and the gate must refuse that body under some row.

## Why

The row `plain_int` refuses `char`, because the compiler sets its signedness. A `std::string` is a container of `char` behind a library type, and the gate saw only the written type, so `std::string` passed while `char` did not. The model has no text type either. The battery's `string_npos` case modelled `std::string` as a Dafny string of Unicode characters, which is not what the bytes are. Bytes have one model, a `seq<uint8>`, and the examples already read text that way. The `throw` message told the bot to use `std::expected`, which does not compile under the pinned toolchain, decision 0030's record. The arena example needed a trusted body that allocates, and the test let a trusted body appear only under a `trusted_only` row.

## What changes

The row `strings` with its pair, and the `string_npos` case on the gate side with a byte-span fix. The `exceptions` row's advice, the examples test, and the enum_cast rule, which now says a flags type is a `bv32`. 75 rules, 61 enforced by the gate.
