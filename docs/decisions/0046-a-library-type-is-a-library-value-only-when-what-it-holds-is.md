# 0046: A library type is a value of the library only when what it holds is

Date: 2026-10-07. Status: decided. Amends 0045, which let a library constructor read any type of the library.

## Decision

Each type argument of a library type must be a number, an enum or a value of the library. Only then is the library type a value of the library. So `std::pair<W, int32_t>` is no value of the library when `W` is a type of the file. A library constructor that copies one through a const handle is no read. An enum counts as a number, because it has no constructor.

A struct of the file with a trivial copy stays no read too. A constructor template of the file can take a non-const reference, and overload resolution then picks it over the trivial copy. `std::as_const(*p)` stays the way.

## Why

C++23 gives `std::pair` and `std::tuple` a constructor from a non-const reference to another pair or tuple. It forwards a non-const `W&` to the constructors of `W`. So the hole of 0045 stays open for each library type that holds `W`. The ninth review showed it with a run: a `W(W&)` of the file changed what a const handle owns. This is decision 0043 again. A library type counts by what it holds.

## What changes

The rule of 0045 walks the type arguments of a library type, and of each pack. The const-edges fixture gains a pair and a tuple of a type of the file.
