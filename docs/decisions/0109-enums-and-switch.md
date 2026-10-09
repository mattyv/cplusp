# 0109: An enum class is a datatype, and a switch over it is a match

Date: 2026-10-09. Status: decided.

## Decision

- An `enum class` of the file whose enumerators have no values written is a type of the subset. Its model is a Dafny datatype with one constructor for each enumerator, in order. It can be a parameter, a local, a result and a field of a struct.
- An enumerator such as `Kind::Small` reads as its constructor, in code and in contracts. In a contract, the name has its enum before `::`.
- `==` and `!=` compare two values of one enum, in code and in contracts. No other operator and no cast takes an enum.
- A `switch` over a value of an enum is a match, with one case for each `case` label. The gate already refuses a switch that misses an enumerator, and a case that falls into the next one with no mark. The translator also refuses a `default`, a fall that `[[fallthrough]]` marks, and several labels on one body. A `break` as the last statement of a case ends the case. A `break` in any other place is refused, as before.
- A statement after the switch stays in the model. When each case returns, no path reaches it. This is correct only because the gate refuses a value that is no enumerator, row enum_cast.

## Why

Three examples stop at an enum or at a switch over one: `control_flow`, `state_machine` and `errors`. The gate already keeps every value of an enum class to its enumerators, so a datatype is an exact model. A match on a datatype is exhaustive in Dafny, which is the C++ switch with one case for each enumerator. I checked the model of the three examples by hand in Dafny.

An enum with values written, such as `bit_flags`, is a set of bits. Its model is a different one, so it waits for a decision of its own.
