# 0140: A pointer to const is an optional

Date: 2026-10-12. Status: decided. Amends 0075 and 0131.

## Decision

- A parameter of type `const T*` is an optional of `T` in the model, when `T` is a scalar or a plain struct of 0137. Null is no value. Otherwise the value is the object that the pointer names.
- In code and in a contract, `*p` reads the value, and `p->f` reads a field of it. Dafny proves that the pointer is not null wherever the code or the contract reads it.
- In code and in a contract, `p == nullptr` and `p != nullptr` test for a value. So does `nullptr` on the left. In a contract, `nullptr` is a word of the grammar.
- At a call, three arguments can go to a `const T*` parameter. They are a pointer parameter of the caller, `nullptr`, and `&x` for a local or a parameter `x` of type `T`. `&x` is the value of `x`.
- A pointer with no `const`, and a pointer tested as a bool, as `if (p)` or `!p`, have no rule yet.
- The sentence for a read that may have no value changes for both kinds. It becomes `the optional may be empty or the pointer may be null here.`

## Why

The survey of the examples that do not prove found that `raw_pointer` and `launder_placement_new` stop at `const int32_t*`. The row raw_pointer keeps a pointer a parameter only, with no arithmetic, no member and no local. The pointer names one object, and the function cannot write through it. The row aliasing refuses a second name that writes the same object in the call, decision 0033. So the object keeps its value for the whole call, as a `const T&` does, decision 0108. A `const T&` that can be null is an optional of `T`.

Dafny gives the same message for an empty optional and a null pointer, because both are the same datatype in the model. So the sentence names both.
