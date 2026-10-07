# 0053: A pointer counts as the object, and a friend of a plain type is plain

Date: 2026-10-07. Status: decided. Amends 0052 on pointers, and 0051 on a friend defined in a plain type.

## Decision

- A pointer to a plain object counts as the object. A call of the library that takes one is a use, as a call that takes the object or a reference is. A C call such as `std::fwrite(&r, sizeof r, 1, f)` reads every byte of `r`.
- A friend defined in a plain type is plain. It is code in the body of the type, so it is out of view. Decision 0048 says the same for a lambda in a plain function. A verified call of it is a call of plain code, decision 0047. A friend with a marker of its own takes that kind. The `friend` in a plain type is out of view too, so the gate does not refuse it as a construct that no row names.
- A verified member of a plain type reads no field of its own type. It is verified code, and verified code reads no field of a plain type. It can call a trusted member, and that member reads the field.

## Why

The review of the 0052 green step found two things. `std::fwrite` and `std::fread` read and wrote a plain object through a pointer, and no row saw them. A pointer is how a C call takes an object, so it is a use for the same reason as a reference. A friend defined in a plain type was refused for the word `friend`, also when it had a trusted marker. The bot cannot change a plain type, so it could not meet the gate.

## What changes

The check of uses takes the pointee of a pointer argument. The kind of a function reads the lexical place of a friend that the type defines, so the regions and the rule on calls agree. A fixture with a call through a pointer, a plain friend, and a trusted friend.
