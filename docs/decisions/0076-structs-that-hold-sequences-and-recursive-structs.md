# 0076: Structs that hold sequences, and recursive structs

Date: 2026-10-08. Status: decided. The fourth step of the fifth slice in 0072. Amends 0064 and 0070 on the bound on a length.

## Decision

- A sequence can hold a struct of the file, as `std::vector<Node>` or `std::span<const Node>`. Its Dafny type is a sequence of the datatype.
- A struct can hold a sequence of a scalar or of a struct of the file. A struct can hold a sequence of itself, as `std::vector<Node>` in `Node`. Its datatype is then recursive.
- A struct that holds a sequence, directly or through a field, is in the subset where a sequence is. That is a parameter only, decision 0064. A local or a result of such a struct has no rule yet. The subset cannot make or write a sequence, so it cannot make such a struct.
- The prelude declares `type Vec<T> = s: seq<T> | |s| < 0x1_0000_0000_0000_0000 witness []`. Each C++ sequence of no fixed extent is a `Vec<T>`. The type holds the bound on the length, so the bound also holds for a sequence in a field or in an element. The bound replaces the line `requires |v| <= 0xFFFF_FFFF_FFFF_FFFF` of 0064. A span of fixed extent keeps the line `requires |v| == N` of 0070.
- In code, `.size()` and `[i]` read a sequence on a field or on an element, as in `n.children[i].prefix[0]`. An element of a sequence of structs passes to a parameter of that struct.
- In a contract, `.size()` and `[e]` read a sequence on a path. A path is a parameter, a field of a path, or an element of a path, as in `n.children[j].prefix.size()`.
- `decreases n` on a struct parameter uses the Dafny order on datatypes. An element of a sequence in a field of `n` is smaller than `n`. So a recursion into `n.children[i]` proves its measure.
- A sequence of `bool` still has no rule, decision 0064. A sequence of an optional, and an optional of a struct, have no rule yet.

## Why

`radix_find` reads a `Node` that holds a byte prefix and a vector of child nodes, and it recurses into a child. A requires line can bound the length of a parameter, but it cannot bound each sequence inside a recursive struct. A type can. One rule for each sequence is simpler than a line for each parameter. The battery case `seq_length` gets the type as its mitigation.

## What changes

The core gains sequences of structs and struct fields of sequences. It reads a sequence on a path in code and in contracts. Its struct table knows which structs hold a sequence. The bound on a length moves from a requires line to the type. The plugin writes the new types and reads. The shell prints `Vec<T>` and the prelude line. The battery case `seq_length` and the skill rule change to the type.
