# 0171: A unique_ptr as a field and by value, and std::move of a local. Step A of slice five of 0165

Date: 2026-10-21. Status: decided. Amends 0094, 0142 and 0168. This is the first of two steps of slice five of 0165. Step B, decision 0172, lets a pure member function call a function of the model.

## Decision

- `std::unique_ptr<B>` of a plain struct or an interface `B` can be a field of a plain struct or of a final class. Dafny reads it as `Option<S_B>`, as 0142 reads a unique_ptr. A contract reads `f_ != nullptr`, `f_->g(a)` and `this->f_`, as 0168 reads a unique_ptr. In code, `f_->g(a)` with `g` const calls `B::g` on the value of the field. Dafny proves that the field is not null there, with the sentence of 0075.
- A call that writes through a field has no rule yet. The sentence is that of 0108, `the call writes a value back, and the translator writes back only to a local or a reference parameter.`
- `std::unique_ptr<B>` can be a parameter by value. It is a value `Option<S_B>` that the function owns. The argument at it is `std::make_unique<D>(a)` of 0168, a call that gives a `std::unique_ptr<B>`, or `std::move(x)`.
- `std::move(x)` of a local or a parameter `x` of type `std::unique_ptr<B>` is in the subset where C++ makes a new `std::unique_ptr` from it. That is at a parameter by value, as the start value of a local, and as the value of a return. Its value is the value of `x`.
- `std::move(x)` can stand in three statements. These are a call that stands alone, decision 0108, the start value of a local, and a return. It can be the value itself, an argument of a call or of a constructor, or the argument of `std::make_unique`. After a call or a local, `x` is null in the model. A later read of `x` fails with the sentence of 0075.
- A parameter can move only in a return, because the model cannot write a parameter. The init list of a constructor is its return, decision 0094. So `f_(std::move(p))` gives the field the value of `p`. A move of a parameter in a call or a local gives the sentence of 0108, `p is a parameter. The translator writes only a local or a reference parameter.`
- A statement that moves `x` reads `x` nowhere else, and moves it only once. C++ does not fix the order of the arguments of a call. So the model cannot know if a read comes before the move or after it. The sentence is `x moves and is read in one statement. C++ does not fix the order.`
- A move in any other place has no rule yet. The sentence is `a std::move of a std::unique_ptr has a rule only in a call that stands alone, the start value of a local or a return.`
- These have no rule yet, as before:
  - `std::move` of any other expression, such as an element of a vector or a struct. The sentence stays `a call to std::move<T>, which has no model in view.`
  - `std::move(x)` at a parameter `const std::unique_ptr<B>&`. C++ makes no new `std::unique_ptr` there, so nothing moves.
  - A write to a parameter by value, and `reset`, `release` and `get`, decision 0142.
  - The return of a local `std::unique_ptr` with no `std::move`, decision 0168.

## Why

The example `decorator` holds the component that it decorates in a field of type `std::unique_ptr<Component>`. It gets the component by value in its constructor, and the caller moves a local into it. A unique_ptr is the one owner of its object, so a move gives the object to the new owner and leaves `x` null. The model says the same, so a read after the move fails as a null read. Two names never share one object. The gate flags a read through `x` after its move, rule `rvalue_references`. It does not flag a null test of `x`, a read in another argument of the same call, or two moves of `x` in one call. So the core refuses every other read of `x` in the statement, and the model needs the gate for nothing here. The reviewer checked this model by hand in Dafny with the whole example `decorator`. The check also had a use after a move and a field read with no null guard.
