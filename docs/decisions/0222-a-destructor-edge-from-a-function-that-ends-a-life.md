# 0222: A destructor edge from a function that ends a life

Date: 2026-10-31. Status: decided. Amends 0218 and 0219. In the call graph of 0218, each function has an edge to each destructor of the file. This is sound, but it refuses too much. A destructor `~Guard() { log_->note(); }` calls through the interface `Log`, and the only override `Quiet::note() const override {}` runs nothing. The edge from `Quiet::note` to `~Guard` made the call come back.

## Decision

A function has an edge to the destructors of the file only when it can end the life of an object. Here an object is one whose destruction can run a destructor of the file. The core takes it that a function can end such a life when one of these holds:

- It is a destructor.
- It has a parameter by value, or a local at any depth, of a type that is not plain.
- It writes a place of a type that is not plain. This includes each write through a `std::unique_ptr`, each write of an element of a vector, and each sort.
- It calls a function that gives a value of a type that is not plain.
- It makes a value of a struct that is not plain.

A plain type holds no object with a destructor of the file. These are the integer types, `double`, `bool`, an enum, a reference and a pointer. A sequence or an optional of a plain scalar is plain too. A struct is plain when it has no destructor and no field is a struct or a `std::unique_ptr`. Each other type is not plain.

## Why

A destructor of the file runs only at the end of the life of an object. C++ ends a life at the end of the scope of a local, and at the end of a parameter by value or a temporary. It also ends a life when a write replaces an object, and when the owner ends. Each of these cases is in one of the rules above, or in a function that the path reaches. So each path that runs a destructor still has an edge to it. The rule takes a struct field as not plain, so that the check needs no recursion over the structs.

## What changes

The core computes, for each function, whether it can end a life, and gives the edges to the destructors only to those functions. Two fixtures hold the cases. In the first, a destructor calls through an interface whose override ends no life, and it proves. In the second, the core refuses a local whose destructor calls back through the interface.
