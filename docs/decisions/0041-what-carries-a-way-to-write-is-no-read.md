# 0041: What carries a way to write is no read

Date: 2026-10-07. Status: decided. Amends 0040, whose reads did not say what the value read may carry.

## Decision

A read of what a const handle gives counts as a read only if its value carries no way to write. A value carries a way to write when it is, or holds, a pointer or reference to non-const, a span of non-const, or a handle. A type of the library counts by its members and its template arguments, as a type of the file does.

- A const method on the object is a read when its result carries no way to write. Else the walk follows the result.
- A copy of the object, and a const reference to it, are reads when the object carries no way to write. Else they are uses that are no read.

## Why

The compiler puts a conversion to const before a const method call and before a copy. The check took that conversion for the end of a read. But const on an object does not reach what its pointer members point to. A const method returned a pointer to non-const, and a copy kept the pointer of the original. A fifth review of the green step of 0038 found both. In verified code the rows `raw_pointer`, `array_span`, `shared_ptr` and `lvalue_references` keep most such types out. A type of a library is not judged, and a team may loosen a row. A loosened row must not open another check.

## What changes

The const-handle check asks of each value whether it carries a way to write before it ends a walk. A test with a header of a library type that carries one.
