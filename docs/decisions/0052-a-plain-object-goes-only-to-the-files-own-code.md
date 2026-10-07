# 0052: A plain object goes only to the file's own code

Date: 2026-10-07. Status: decided. Amends 0051 on what verified code may do with a plain type.

## Decision

- **No value of a plain type, and no value that holds one.** Verified code makes no object of a plain type. It makes no object of a library type that holds one either, by the walk of decision 0046. So `std::vector<Record>` in verified code is a use of `Record`.
- **Only the file's code gets a plain object.** Verified code can pass one, or a reference to one, to a function of the file. That function is judged by its own kind. A call of the library that takes one is a use, because the library can read or copy it. `std::bit_cast` and `push_back` are two such calls.
- **A read that the compiler writes counts.** A structured binding reads the fields of its object in code that the compiler writes. That read is a use too.
- **A plain member is plain for overrides.** Decision 0047 refuses a plain override of a function that is not plain. A member of a plain type with no marker of its own is plain, written by the file or by the compiler.
- **A member with its own marker keeps its declaration in view.** Its declaration is verified, as 0039 says, also inside a plain type.

## Why

The review of the 0051 green step found four ways past it. A structured binding by reference read the fields. `std::bit_cast` read the whole object. A plain override defined in another file ran from a verified virtual call. A verified member inside a plain type lost the findings of its declaration. A list of the ways to read a field grows with each review, as the lists before it did. The library reads what verified code hands it. So the line is at the call into the library, as decision 0050 put it for a function pointer.

## What changes

The check of uses takes a library type that holds a plain type and a call of the library with a plain argument. It reads the code that the compiler writes too. The rule on overrides reads the kind of a member. A member with its own marker gets a verified region over its declaration. A fixture with the five ways.
