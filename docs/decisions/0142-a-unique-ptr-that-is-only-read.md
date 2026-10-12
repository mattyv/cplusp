# 0142: A unique_ptr that the code only reads is an optional

Date: 2026-10-12. Status: decided. Amends 0140 and 0141.

## Decision

- `std::unique_ptr<T>` is in the subset when `T` is a scalar or a plain struct of 0137, in three places. It can be a parameter of type `const std::unique_ptr<T>&`. It can be the result of a function. It can be a local that a call or `std::make_unique` sets.
- The core gives it the type `Own(T)`. Dafny reads it as `Option<T>`, as a pointer of 0141. Null is no value.
- `*p` and `p->f` read the value, and Dafny proves that it is not null there. `p == nullptr` and `p != nullptr` test for a value, in code and in a contract.
- `std::make_unique<T>(x)` for a scalar `T` is a value of `x`.
- Two unique_ptrs do not compare, as two pointers do not, decision 0141. Any other operator with a unique_ptr operand has no rule.
- A write through a unique_ptr, as `*p = e`, has no rule yet. So has a move, `reset`, `release`, a unique_ptr parameter by value and a unique_ptr with no const by reference.

## Why

The survey of the examples that do not prove found that `unique_ptr` and `raw_allocation` stop at `std::unique_ptr<int32_t>`. A unique_ptr is the one owner of its object. Nothing else names the object, and the code above only reads it, so the value stays the same while the unique_ptr lives. That is the value model of 0029. The object lives as long as its owner, so a local can hold one, which a raw pointer cannot, decision 0140. So the core keeps `Own` apart from `Ptr`, and a raw pointer stays a parameter only in the core too.
