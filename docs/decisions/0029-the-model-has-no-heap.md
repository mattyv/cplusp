# 0029: The model has no heap. An object is a value

Date: 2026-10-05. Status: decided. Amends the Dafny half of 0028, which modelled a C++ class as a Dafny class.

## Decision

The model has no heap. A C++ object is a Dafny `datatype`, and so is the `State` that holds the globals. A const member function is a `function` over the value. A non-const member function is a method that takes the object in and gives it back, `c' := bump(c)`. In the C++ contract `old(x)` is the value on the way in and `x` the value on the way out. A pointer or a `unique_ptr` is an `Option<T>` value. An interface is an opaque type whose contract is the only thing known about it. An implementation proves it meets that contract on its own type. A trusted function is a method with no body, as before. No model uses `class`, `trait`, `modifies`, `reads`, `old` or `new`, and a test keeps it so.

A value model cannot see two names for one object. So the C++ side closes aliasing. A reference is a parameter only, never a member and never a local, under the row `lvalue_references`. Two non-const reference parameters of one type always carry `requires &a != &b`.

## Why

Dafny classes bring the heap: frames, `modifies`, `reads`, `old`, constructors and `Valid()` with a `reads` clause. That is the part of Dafny a bot gets wrong, and the part that makes a model long. Datatypes and functions are the part it gets right, and they verify fast. The subset already keeps aliasing out of verified code in every way but two, a reference member and a reference local. The gate can refuse both. The one alias left, two reference parameters to one object, is a precondition the caller proves. With those closed, a value is an exact model of an object. VeriFast and Verus take the same shape, a predicate over the fields and the object in and out, so the choice holds across provers. The C++ contract does not change. 0028 stands for the C++ side.

## What changes

The row `lvalue_references` becomes `restrict` with a gate matcher and a sample pair. The skill's rules on references, values, state, pointers, moves, slicing and interfaces say value where they said object. Every `example.dfy` and every `mitigated.dfy` is a value model, and the test `the_model_has_no_heap` refuses a heap construct in them. The naive models of the battery stay as the bot wrote them.
