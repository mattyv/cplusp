# 0170: A vector of unique_ptr of an interface. Slice six of 0165

Date: 2026-10-21. Status: decided. Amends 0064, 0145, 0148, 0160 and 0168. This is slice six of 0165. The reviewer checked the model in Dafny before the tests.

## Decision

- `std::unique_ptr<B>` of a struct or an interface `B` is an element of a vector. Dafny reads the vector as `seq<Option<S_B>>`, with the bound of 0164. The vector is a parameter `const std::vector<std::unique_ptr<B>>&`, decision 0064, a parameter `std::vector<std::unique_ptr<B>>&` on the modifies line, decision 0145, or a local, decision 0160.
- A local `std::vector<T> v;` with no initial value is the empty sequence, for every `T` of the subset. This includes a vector of a plain struct of 0163. This amends 0160.
- A call that passes a local vector to a parameter `std::vector<T>&` writes the vector back to the local, as 0108 writes a local. This amends 0160.
- `v.push_back(std::make_unique<D>(a))` adds `Some(f_D'B(d))`, where `d` is the value of the constructor of `D`, decision 0168. The constructor runs before the `push_back`. This amends 0148 for this form only.
- `v[i] != nullptr` and `v[i]->f(a)` read the element as a unique_ptr of 0168, in code and in a contract. Dafny proves that `i` is in range and that `v[i]` is not null, with the sentences of 0064 and 0075. A contract line that reads `v[i]->f()` stands below a line that says `v[i] != nullptr`.
- `v[i]->f(a)` with `f` not const writes the new value back to the element: `v' := v'[i := Some(t)]`. The index holds no call and reads no place that the call writes. Otherwise the translator refuses the call with `the index reads a value that the call writes: the translator has no rule for it yet.`
- These have no rule yet:
  - An assignment to an element. The sentence is `an assignment to a unique_ptr element: the translator has no rule for it yet.`
  - A range-for over such a vector. The sentence is `a range-for over a vector of unique_ptr: the translator has no rule for it yet.`
  - `*v[i]` at a `B&` parameter, with the sentence of 0108.
  - `std::move` of an element, `erase`, `insert`, `pop_back`, `resize`, `clear`, and a result or a field of this type.
- A `std::unique_ptr` is in the subset as an element of a vector and in the three places of 0142, and nowhere else.

## Why

The examples `shape_area_sum` and `command` keep their objects in a vector of `std::unique_ptr<B>` and call through each element. Each element is the one owner of its object, and the subset moves no element, so two elements never name one object. A write through one element changes that element only, and the callee cannot reach the vector. So the length and the other elements keep their values. The model reads the index twice, at the call and at the write, so it must not change between the two.
