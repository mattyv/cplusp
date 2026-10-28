# 0198: A moved field is null at once

Date: 2026-10-28. Status: decided. Amends 0197. The review of 0197 found that a later value of the init list could read `other.f` after the move and see the value from before it.

## Decision

In the init list of a move constructor, `other.f` is null right after the init of the field that moves it. C++ runs the inits in the order of the fields. So a later value of the init list that reads `other.f` reads null. The model gives `other.f` its null at that place, not after the whole init list. Dafny then checks a read through `other.f` there, with the sentence `the optional may be empty or the pointer may be null here.`

A move constructor with more than one parameter has no rule for this move. It keeps the sentence of today.

## Why

0197 said that `other.f` is null after the init list. That is true at the body, but not between two inits. A field such as `h_(other.c_ != nullptr)` after `c_(std::move(other.c_))` is false in C++, and the model said true. A read `other.c_->v` there has no defined behaviour in C++, and the model said it read the old value. The proof must follow the order of C++.

## What changes

The plugin writes the null of `other.f` right after the init local of the field that moves it. It also refuses the move in a move constructor with a second parameter, where it stopped with an error before. The wrong fixture of 0197 gains the two cases. The refuse fixture of 0197 gains the second parameter.
