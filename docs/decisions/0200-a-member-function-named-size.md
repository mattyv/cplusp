# 0200: A member function named size

Date: 2026-10-29. Status: decided. Builds on 0064, 0078, 0090 and 0191. Amends 0064, 0078 and 0191 on how a contract reads `.size()`, `.empty()` and `.back()`. Four examples had to rename a member function `size()` so that a contract could call it, and the example `multiple_inheritance` has an interface `Sized` with `size()`.

## Decision

In a contract, `o.size()`, `o.empty()` and `o.back()` read the object `o` by its type. When `o` is a sequence, they are the length, the test for no element and the last element, as before. When `o` is a struct, a class or an interface, they are a call of the member function of that name, decision 0090. A member function with one of these names then works in a contract as any other.

The lexer keeps each of the three words as a token of its own, with the id of its name. The parser keeps both forms. The translator picks one by the type of `o`, once it knows that type.

## Why

`size()`, `empty()` and `back()` are the common names in C++ for a container and for a class that wraps one. The contract language read them only as words of a sequence. So `s.size()` of a class gave `the contract line has a form the translator cannot read.`, and the bot had to rename a member to call it. The translator knows the type of `o` when it reads the line, so the choice belongs there.

## What changes

The core gives the three tokens the id of their name, and the parser keeps both forms of each. The translator reads the form of the sequence for a sequence and the call of the member for any other type. The shell gives each token its id. The plugin needs no change. Three fixtures follow the form of 0178. The example `multiple_inheritance` uses `s.size()` of its interface.
