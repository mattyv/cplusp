# 0197: The pointer to implementation

Date: 2026-10-28. Status: decided. Builds on 0142, 0171, 0178, 0179 and 0186. The example `pimpl` keeps the data of a class in a struct behind a `std::unique_ptr` field. It makes the struct with `std::make_unique`, writes through the pointer, defines its destructor `= default` out of line, and moves the pointer in its move constructor.

## Decision

`std::make_unique<S>(args)` of a plain struct `S` with a constructor of the model calls that constructor, decision 0094. The value is the struct that the constructor gives, in a `std::unique_ptr`. Each argument has the type of its parameter, as 0170 says for a class over an interface. It can be the start value of a local, a value in the init list, or the value of a field write.

In a member function that writes its object, `f->g = e` and `f->g op= e` write the field `g` of the struct that the `std::unique_ptr` field `f` owns. The value `e` holds no call. Dafny proves that `f` holds a value. The sentence is `the optional may be empty or the pointer may be null here.`

A class can declare a destructor with a contract, and the file can define it `= default` out of line. That is a destructor with an empty body, decision 0178. Its contract stands on the declaration. A destructor `= default` in the class stays no destructor, decision 0179.

In the init list of a move constructor `T(T&& other)`, `f(std::move(other.f))` of a `std::unique_ptr` field `f` gives the new object the value of `other.f`. After the init list, `other.f` is null, as the C++ library says for a moved `std::unique_ptr`. A move constructor `= default` is the same as one that moves each `std::unique_ptr` field this way and copies each scalar field. The rules of 0179 hold for both: the struct has a destructor, and the constructor lists `other` on its `modifies` line.

These keep the sentence of today:

- a move constructor `= default` of a struct with a field of any other type,
- `std::move(other.f)` of a field of any other type,
- a write through a `std::unique_ptr` field of a parameter.

## Why

The pointer to implementation is the common way in C++ to hide the data of a class from its header. The model has each part of it near. A `std::unique_ptr` of a struct is an optional, decision 0142. The model has a write through a local `std::unique_ptr`, decision 0186. It has a destructor with a contract, decision 0178, and a move constructor, decision 0179. The C++ library says that a moved `std::unique_ptr` is null, so the model knows the value of `other.f` after the move.

## What changes

The core reads a write through a `std::unique_ptr` field of the object. The plugin writes `std::make_unique<S>(args)` as the call of the constructor. It writes the destructor `= default` out of line as an empty body. It writes the move of a `std::unique_ptr` field of `other` as its value and then the null of `other.f`. The plugin also writes a move constructor `= default` in that form. This is a trusted part of the plugin. The shell prints the write. Three fixtures follow the form of 0178. The example `pimpl` lists `other` on the `modifies` line of its move constructor, and its destructor gets the contract `ensures true`. It proves.
