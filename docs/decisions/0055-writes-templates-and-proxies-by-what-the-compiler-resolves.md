# 0055: Writes, templates and proxies count by what the compiler resolves

Date: 2026-10-08. Status: decided. Amends 0033 on what can write, 0036 on templates, and the row `lvalue_references`.

## Decision

- A non-const rvalue reference can write, as a non-const lvalue reference can. The gate has one test for a type that can write, and every check asks it. The check of aliases had its own test, which took the rvalue reference. The check of effects had another, which did not.
- A check that reads types judges each instantiation of a template, as 0036 says. The checks of iterators and of multiple inheritance read what the author wrote, so a deduced iterator or two bases through template parameters passed. They read each instantiation now. A check that reads only the spelling, such as `mutable`, stays as it is.
- A proxy of the library is a reference in disguise. A local or a field of such a type is a finding of `lvalue_references`, by its deduced type. The proxies are the `reference` types of `std::vector<bool>` and `std::bitset`, `std::reference_wrapper`, and a `std::tuple` or `std::pair` that holds a reference. A loop variable of a range-for stays allowed, as a reference loop variable is. To copy the value, write its type: `bool bit = v[0];`.

## Why

The seventh outside review found three ways past the gate, each with a witness. `next(std::move(x))` beside a read of `x` gave true under clang and false under gcc. A template took a vector's iterator, cleared the vector and read through the iterator, and AddressSanitizer saw the use after free. `auto bit = v[0]` on a `std::vector<bool>` kept a second name for the bit, and the read after `v` changed saw the new value. In each, the gate read the spelling, and the compiler resolved something else.

## What changes

The test for a type that can write takes a non-const rvalue reference. The checks of iterators and multiple inheritance read instantiations. The row `lvalue_references` gains matchers on the deduced type. Four sample pairs gain a line each, and `lvalue_references` two.
