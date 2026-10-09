# 0107: The name and the value of a constant, and the sentence of a shift

Date: 2026-10-09. Status: decided. Amends 0106.

## Decision

- A named constant reads as its value in each integer type. This includes an unsigned value with the top bit set, such as `uint8_t 200`, and the minimum of a signed type, such as `int8_t -128`. Code and contracts read the same value.
- A name in a contract reads as a constant at the scope of the file only when C++ finds that constant from the function. C++ looks in the function, its class and the bases of the class, and its namespaces first. A field, a static member or a namespace constant with the same name hides the constant of the file. The name then reads as it would with no constant of the file. A field reads as the field. For any other name, the translator refuses the contract with `NAME in the contract is no parameter.`
- When Dafny cannot prove the condition of a shift, `prove` says `the shift amount may be negative or not below the width of the type.` at the line of the shift.

## Why

The review of the 0106 shell found two programs that proved but were wrong:

- An unsigned constant with the top bit set read as a different value in code. `constexpr uint8_t kByte = 200` read as 56.
- A constant of the file replaced a field, a static member or a namespace constant of the same name. Only the plugin knows the scopes, so it gives the shell the names that each function hides.

A constant equal to the minimum of its type gave the message that its value may not fit. That message is wrong for a correct program.

The sentence of 0106 named only the width. An amount can also be negative, and the old sentence did not tell the reader that fault.
