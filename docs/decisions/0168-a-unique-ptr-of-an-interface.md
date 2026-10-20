# 0168: A unique_ptr of an interface. Slice four of 0165

Date: 2026-10-20. Status: decided. Amends 0142 and 0166. This is slice four of 0165. Slice three, a virtual function that is not `const`, comes after it, because the example `factory` needs this slice only.

## Decision

- `std::unique_ptr<B>` of an interface `B` is in the subset in the three places of 0142. It can be a parameter `const std::unique_ptr<B>&`, the result of a function, or a local that a call or `std::make_unique` sets. Dafny reads it as `Option<S_B>`.
- `std::make_unique<D>(a)` of a final class `D` over `B`, as a `std::unique_ptr<B>`, is `Some(f_D'B(d))`. Here `d` is the value that the constructor of `D` gives, decision 0094, or `S_D()` for a class with no field and no constructor. The constructor is a method, so its call stands alone before the `Some`, decision 0104. This holds also at a call argument, where C++ makes a temporary `std::unique_ptr<B>`. The upcast of 0166 gives the value of each virtual function.
- `p->f(a)` calls `B::f` on the value of `p`, in code and in a contract. Dafny proves that `p` is not null there, with the sentence of 0075.
- `std::make_unique<D>(a)` held as a `std::unique_ptr<D>` has no rule yet. A `std::unique_ptr<D>` that a call or a name gives, as a `std::unique_ptr<B>`, has no rule yet either. The sentence is `a std::unique_ptr of a class as a std::unique_ptr of its interface: the translator has no rule for it yet.` A class with no check has no upcast, so `std::make_unique` of it stops Dafny, as a call argument does in 0166.
- The other rules of 0142 hold. A move, `reset`, `release` and a write through the unique_ptr have no rule yet.

## Why

The example `factory` makes a shape with `std::make_unique` and calls it through `std::unique_ptr<Shape>`. A unique_ptr is the one owner of its object, and the code only reads it. So the value model of 0142 holds for an interface too. The object is a value of `D`, so its upcast is the value of the interface, as at a call argument in 0166.
