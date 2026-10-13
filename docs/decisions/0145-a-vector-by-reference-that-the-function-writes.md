# 0145: A vector by reference that the function writes, step one: element writes

Date: 2026-10-13. Status: decided. Amends 0064 and 0108. The user chose this direction on 2026-10-13.

## Decision

- A parameter of type `std::vector<T>&` is in the subset when the modifies line names it. `T` is a scalar type of a sequence other than bool. Its type in the core is `MutSeq(T)`, and Dafny reads it as `seq<T>`.
- It takes its value in and gives it back, as a reference parameter of 0108 does. The method has the parameter `v` and the result `v'`. The body starts with `v' := v`, and reads and writes `v'`.
- In code, `v.size()` and `v[i]` read the value. `v[i] = e` writes one element: `v' := v'[i := e]`. Dafny proves that each index is in range. So the length of the vector does not change in this step.
- In a contract, a requires line reads the value before the call, and an ensures line reads the value after the call. `old(v)` reads it before the call, as in 0108. `v.size()`, `v[i]` and the slices of 0085 read it as a sequence.
- Each method with such a parameter requires that its length fits `size_t`, as 0064 says for each sequence.
- These have no rule yet: a call of a member function of the vector, such as `push_back`, `resize` or `clear`. Also `v[i] op= e`, `++v[i]`, a reference to an element and an iterator. Also a call that passes the vector to a parameter of this type. Also `std::vector<bool>&` and a vector of a struct.

## Why

The user chose vectors by reference as the next block. Two examples write a vector by reference: `variable_index` writes one element, and `sorted_insert` also appends. This step covers the first. A function that writes elements is a function from the old sequence to the new one. So the value model of 0029 holds, as it does for 0108. The gate refuses two names for one vector in a call, decision 0033. So the vector is one value for the whole call.
