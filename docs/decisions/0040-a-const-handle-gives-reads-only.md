# 0040: A const handle gives reads only

Date: 2026-10-07. Status: decided. Amends 0033 and 0038, which listed the ways a write leaves a const handle.

## Decision

The const-handle check no longer lists the ways out of a const handle. It lists the ways a read uses what a const handle gives, and it refuses every other use.

- **An object.** A const handle owns it. Read its value, bind it to a const reference, or call a const method on it. Take a member or an element of it and go on. A view of const elements may take it.
- **A pointer.** It reaches through a const handle. Dereference it or index it and go on. Compare it, test it, or convert it to a pointer to const.
- **A span.** It reaches through a const handle. Index it and go on, call a const method on it, or convert it to a span of const elements.
- **Any other use is refused.** A store, an argument, a return, a capture, a brace list and a cast are other uses. So is a use the check does not know.

## Why

Decision 0033 refused a write through a const handle, and decision 0038 refused a return of one. Each named a way out. Four reviews of the green step of 0038 found more. A capture initializer, a member initializer, a brace list, a functional cast, an argument by value, an assignment of a class. C++ has more ways to carry a value than any list holds. The ways to read one are few. A check that knows the reads and refuses the rest fails closed, as decision 0036 asks of every analysis.

## What changes

The const-handle check follows a value from a const handle to the first node that is no step of a path. It refuses that node unless it is a read above. The row `unique_ptr` keeps its limit, because the limit already says const access only. A pin for each spelling the reviews found, and the reads that must stay clean.
