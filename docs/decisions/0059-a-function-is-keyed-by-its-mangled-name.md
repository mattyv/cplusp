# 0059: A function is keyed by its mangled name, and a Dafny name C++ cannot write

Date: 2026-10-08. Status: decided. Amends 0058 on the key of a function and on the Dafny names.

## Decision

- The plugin keys a function by its Itanium mangled name. The mangled name tells overloads, namespaces and internal functions apart. A call and the definition get the same key.
- Some functions have no mangled name, such as an `extern "C"` function, a template, a constructor or a destructor. Each keeps the key of 0058: its qualified name, then `@` and the place of its definition. A mangled name has no `@`, so the two kinds of key never clash.
- A Dafny name that the shell makes up has a `'`, which C++ cannot write in a name. A parameter with no name is `c_'N`, for its place N. When two or more functions share a plain name, each gets a number in the order of the file: `c_name'1`, `c_name'2` and so on. So no made-up name can clash with a name that the author wrote.

## Why

The review of slice 2 found two overloads that one macro writes. The place of a macro body is the place where the macro expands. So both overloads got one key, and Dafny refused the file for two methods with one name. The same review found that `c__0` for a parameter with no name clashed with a parameter that the author called `_0`. The core then refused legal C++ as a name declared twice.

## What changes

The plugin makes a mangle context and keys each function and each callee by it. The shell names a parameter with no name `'N` and adds `'k` to an overload. Nothing changes in the core.
