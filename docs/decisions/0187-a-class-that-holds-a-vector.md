# 0187: A class that holds a vector

Date: 2026-10-25. Status: decided. Builds on 0076, 0094, 0096, 0160, 0179 and 0185. Amends 0076 on where a struct that holds a sequence can be, and 0094 on its constructor. The example `ring_buffer` keeps its elements in a vector field, and its member functions write one element at a time.

## Decision

A struct or a class that holds a sequence, directly or through a field, is a value. It can be a local, a parameter by value, the result of a function and the object of a constructor. A copy of it is a value of its own, as for any struct. Decision 0076 kept it a parameter only, because the subset could not make or write a sequence then. Decisions 0148, 0160 and 0185 can make and write one now.

A constructor can start a vector field in its init list with `f(n, x)`, a vector of `n` copies of `x`, as 0185 reads a local. A vector field that has no default member initializer, and that the init list does not name, starts empty, as C++ says. The init list runs in the order of the fields, as C++ says, also when a value of it has a side effect.

In a member function that writes its object, `f[i] = e` writes the element `i` of a vector field `f`. Dafny reads it as `this' := this'.(f := this'.f[i := e]);`. Dafny proves that `i` is in range. The sentence is `the index may be out of range.` The function reads `f[i]`, `f.at(i)` and `f.size()` as a `const` member function does, decision 0076.

These have no rule yet:

- `f.push_back(e)`, `f.at(i) = e` and an assignment of the whole field, in a member function. They keep the sentence of today.
- a vector field with a default member initializer. Its constructor keeps the sentence of today, `CXXConstructorDecl: the translator has no rule for it yet.`
- such a struct in an optional, a pointer, a `std::unique_ptr`, or a vector that the code makes or writes. The sentence of 0164 changes to `a struct that holds a sequence has no rule yet in an optional, a pointer, a unique_ptr, or a vector that the code makes or writes.`

## Why

A class that keeps its data in a vector is the common form of a container in C++. The model is a datatype with a sequence field, as 0076 gives it. A write to one element is a new value of that field. Dafny proves the index of each write, and C++ gives undefined behaviour when the index is out of range.

## What changes

The core no longer refuses such a struct as a value. It reads the element write of a vector field. The plugin writes `f(n, x)` in an init list as a vector of copies, and an unnamed vector field as an empty vector. It also writes the element write in a member function. The shell prints the new sentence. Three fixtures follow the form of 0178. The fixture `model-nodes-refuse.cpp` of 0076 becomes `model-nodes-value.cpp`, because its forms now translate. The core test of 0094 for such a constructor now gives a model. The example `ring_buffer` gets its companion file, with the facts about `%` as lemmas, and one `apply` line of 0167 in `push` and in `pop`. Each lemma names the slot itself, not the head plus an index, so that the prover can match it to each slot of the code. The example `ring_buffer` proves.
