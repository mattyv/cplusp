# 0044: An owning container counts by all its type arguments

Date: 2026-10-07. Status: decided. Amends 0043, which said an owning container counts by its element types alone.

## Decision

A container that owns its elements counts by all its type arguments: the element types, the comparator, the hasher and the allocator. A copy of the container copies each of them.

A constructor of the library reads an argument only when the argument's type is the type it builds, or one of that type's type arguments. Any other constructor may call a method of the file on what it is given.

## Why

A copy of `std::map<int32_t, int32_t, Cmp>` copies `Cmp`, and a comparator that holds a pointer to non-const carries it into the copy. The build counted every type argument, which is the safe reading, and the seventh review found the text of 0043 narrower than the code. The same review found two constructors that do more than copy. The engine `std::mt19937` calls `generate` on a seed sequence of the file. `std::thread` copies a callable into state its fields do not show. A result that carries no way to write says nothing of what a constructor did to its arguments.

## What changes

The text follows the code for containers. The constructor rule narrows to a copy of the same type or of a type argument. A copy of `std::pmr::vector` is refused, because its allocator holds a pointer, and `std::as_const` is the way.
