# 0213: A function keeps its ensures lines

Date: 2026-10-29. Status: decided. Amends 0090 and 0165. The example `type_erasure` checks `Model<T>::area()` against `Concept::area()`. The ensures line of `Concept::area()` is `0 <= result <= 1000000`. The function of `Model<T>::area()` is the function of `T::area()` on a field. Dafny proves the bound in the method of `T::area()`, but the function of it holds no ensures line. So the check, two calls away from the bound, fails.

## Decision

Take the function in the model of a pure member function, decision 0090. It has the ensures lines of the member function, as Dafny reads them in its method. Dafny proves each line on the function from its body. The line `result == F(params)` of 0090 stays on the method only. The function of 0205, which is the value of an ensures line, has that line only.

## Why

A caller and the check of an override read the function, not the method. With the ensures lines on the function, each one reads the promise of the member function at once, without the body. The lines add no trust, because Dafny proves them. A function from an ensures line has no body to prove other lines from, so it keeps the one line that defines it.

## What changes

The shell prints the ensures lines on the function of a pure body, with its result named `result`. One fixture holds the shape of the example.
