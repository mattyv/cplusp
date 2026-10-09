# 0115: Why an order of enums has no rule, and more forms of the enum_cast row

Date: 2026-10-09. Status: decided. Amends 0114.

## Decision

- The refusal of `<`, `<=`, `>` and `>=` on enums in a contract stays. Its reason in 0114 was false. Dafny reads such an order as an order of rank that it does not know. It proves neither `Kind::Small < Kind::Large` nor the opposite. So a true C++ line could not prove, but no false line could prove. The refusal gives a clear sentence in place of a failure that the bot cannot explain.
- The row `enum_cast` also bans three more forms. It bans a cast from another enum, and a cast to a pointer or a reference to such an enum. It also bans a use of `std::bit_cast` to such an enum that is no call, such as its address. A cast whose kind changes nothing, such as `static_cast<Kind>(k)` of a `Kind`, stays allowed.
- Two more forms stay open, and docs/soundness.md records them. A `std::bit_cast` to a type that holds such an enum can make a field that is no enumerator. A template in a header of the system paths can cast, because the gate judges no system header.
- The translator drops a struct with a field of an enum whose name Dafny cannot read, with the enum. The struct gives no refusal of its own.
- Two case blocks of one switch cannot declare locals with the same name yet. The rule of 0058 that each name is declared once in a function holds across the cases.

## Why

The second review of the enum step found three casts that the first row let through, and a panic on a struct. It also tested the reason of 0114 in Dafny and found it false. I tested it too: Dafny proves neither `A < B` nor `!(A < B)` for a datatype `A | B`.
