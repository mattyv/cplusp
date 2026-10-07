# 0051: A type can be plain

Date: 2026-10-07. Status: decided. Amends 0039, which gave a marker to a function only.

## Decision

A class or a class template takes `CPLUSP_PLAIN(why)`. Its fields, its static members and its nested declarations are out of the gate's view. Each of its member functions is plain, written or written by the compiler, and so is each member defined outside the class. A member with a trusted marker of its own is trusted.

Verified code touches no plain type. It makes no object of one, as a variable, a temporary, a copy or a base. It reads no field and no static member of one. It can hold a reference or a pointer to one and pass it on. It can call a trusted member, because that member has a contract. A call of a plain member is a call of plain code, decision 0047.

A trusted marker on a type stays refused. The message names both places that take a marker.

## Why

Old code keeps its types outside its functions. With a marker on functions only, each `int` field of an old type was a finding in verified code. The trial on the radix tree had six of them in its tests and its driver. A type that the bot may not change could not pass.

The rule on objects and fields keeps it sound. Decision 0047 already refuses the constructors, the copies and the destructors of a plain type that verified code would run. A field read runs no call. The rows `plain_int` and `strings` match a written type, so a read of an `int` field carries no finding of its own. Verified code reads only what has a contract, and the contract of a trusted member is the way in.

## What changes

The plugin honours a plain marker on a type, with a plain region over the class and over each member defined outside it. A check refuses each object, field read and static member read of a plain type in verified code. A fixture with a plain type, plain code that uses it, and four uses from verified code.
