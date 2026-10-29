# 0212: A move of a value and a constructor template

Date: 2026-10-29. Status: decided. Builds on 0073, 0094, 0171 and 0188. The example `type_erasure` moves a parameter `T value` into a field with `std::move(value)`, and its class `Shape` has a constructor template `template <typename T> explicit Shape(T value)`.

## Decision

- `std::move(x)` of a local or a parameter `x` whose type is trivially copyable is the value of `x`. A move of such a value copies it, so `x` keeps its value after the move. A value that is not trivially copyable keeps its sentence: `a call to std::move<T &>, which has no model in view.`
- A member function template of a class that is no template has a rule when the file makes an instance of it. Each instance is a member function, or a constructor, of the class, with its own key, decision 0188. The contract lines above the template are the contract of each instance. A class with such a template is a struct of 0073 when each instance has a rule. A template with no instance keeps its sentence.

## Why

For a trivially copyable type, C++ makes a move the same as a copy, C++23 [class.copy.ctor]. So the value and the source after the move are what the model reads. A constructor template makes a family of constructors, and the file uses only some of them. Each instance is a function that clang gives in full, as for a class template, decision 0188.

## What changes

The plugin reads such a move as the value, and writes each instance of a member function template as a member function of the class. The core needs no change. Three fixtures follow the form of 0178.
