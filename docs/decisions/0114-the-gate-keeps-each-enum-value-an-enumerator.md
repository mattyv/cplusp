# 0114: The gate keeps each value of an enum class an enumerator

Date: 2026-10-09. Status: decided. Amends 0109.

## Decision

- A new gate row, `enum_cast`, bans a conversion to an enum class whose enumerators have no values written. The row covers each form: `static_cast`, a C cast, a functional cast, a brace initialization from an integer such as `Kind{b}`, and `std::bit_cast`. A ban row holds in trusted code too. To make an enum from a number, a function switches on the number and returns an enumerator for each case.
- Decision 0109 said that a gate row already kept these values to the enumerators. No row did. This row makes the model of 0109 exact. One gap stays, and docs/soundness.md records it: a trusted function can still copy bytes into an object that holds such an enum.
- The translator refuses `<`, `<=`, `>` and `>=` with an operand of an enum type in a contract. The sentence is that of a form it cannot read. Dafny reads them as an order of terms, and that order is never true for two enumerators. So a line such as `k < Kind::Large ==> result` was true in Dafny for each `k`, and false in C++ when `k` is `Kind::Small`.
- A case body can be one block in braces, `case Kind::Small: { ... } break;`. A local of a case needs the braces in C++.
- A contract cannot yet name an enumerator of two enums with the same plain name. The translator refuses the line with the sentence of a form it cannot read. This waits.

## Why

The review of the 0109 shell found a program that proved and was wrong. A trusted function cast the byte 7 to `Kind`. Its caller proved that a switch on the result never reached the line after the switch. The compiled program reached it. The user chose the gate row over a promise of each trusted function, and over an extra constructor for a value that is no enumerator.
