# 0192: A scalar temporary bound to a const reference

Date: 2026-10-25. Status: decided. Builds on 0175, 0181 and 0191. The example `stack_template` calls `s.push(1)`, and `push` takes `const T&` with `T` as `int32_t`.

## Decision

A temporary of a scalar type, bound to a `const T&` parameter, is its value. This is the rule of 0181 for a temporary of a plain struct, for a scalar. The model already reads a `const T&` parameter of a scalar as its value, decision 0175.

A temporary that converts its value, as an `int16_t` at a `const int32_t&` parameter, has no rule yet.

## Why

The temporary is a new object. No other name can see it or change it. It lives to the end of the full expression, and the callee only reads it. So the call sees the same value as a call with a named local. A scalar has no destructor, so its end does nothing.

## What changes

The plugin writes a scalar temporary at a `const T&` parameter as its value. The core and the shell need no change. The example `stack_template` is the test, through the test of 0191.
