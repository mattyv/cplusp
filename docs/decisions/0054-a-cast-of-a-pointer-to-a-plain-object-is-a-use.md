# 0054: A cast of a pointer to a plain object is a use

Date: 2026-10-07. Status: decided. Amends 0053, which counts a pointer as the object when the library takes it.

## Decision

- Verified code that turns a pointer to a plain object into a pointer of another type uses the object. The cast can be written or made by the compiler, and it is a use at the cast.
- A `const void*` or a `const std::byte*` keeps no type. After the cast no callee can be judged on what it gets, the file's own code as little as the library.
- A pointer to a plain object passed as its own type stays as 0052 and 0053 say. It can go to a function of the file.

## Why

The review of the 0053 green step found two ways past it. Two `static_cast` steps through `const void*` gave `std::copy_n` the bytes of a plain object. A verified function with a `const void*` parameter took `&r` from its caller and gave it to `std::fwrite`. In both, the pointer lost its type before the library got it. The cast is the one place where the type is still there, so the cast is the use.

## What changes

The check of uses reads each cast whose source is a pointer to a plain type and whose target is another pointer type. A fixture with the two ways.
