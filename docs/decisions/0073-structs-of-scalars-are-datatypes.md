# 0073: A struct of scalars is a Dafny datatype

Date: 2026-10-08. Status: decided. The second step of the fifth slice in 0072.

## Decision

- A struct whose fields are each a scalar of the subset, or such a struct, is a Dafny `datatype`. It has one constructor, and one field for each field of the struct. A value of it is a value, as 0029 says, and a copy is the same value.
- A struct is in the subset as a parameter by value or by const reference, as a local and as a result.
- In code, `p.x` reads a field. A braced list that gives each field a value, such as `Point{a, b}` or `{a, b}`, makes a value. A braced list that leaves a field out has no rule yet.
- A copy of a struct to a parameter of the same struct keeps the value, as the copy of a sequence in 0070 does.
- In a contract, `p.x`, `result.x` and `b.hi.x` read fields of a parameter or of the result. A field that the struct does not have is refused.
- A write to a field and a member function have no rule yet. Neither has a struct with a field of another type, or a struct with a constructor.

## Why

`radix_find` reads the fields of a node. A struct of scalars is the smallest step toward it, and it needs no heap: the value model of 0029 holds.

## What changes

The core gains the struct type, field reads, braced values and the copy of a struct. It also gains field reads in contracts, and a table of the structs of a file to type them. The plugin writes each struct and its fields. The shell prints each datatype.
