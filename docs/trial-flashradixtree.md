# Trial: FlashRadixTree

The first real file through the gate. The plan's checklist asks for a run on real hot-path code, to tune the decisions from the noise. This is the record of the first run, on 2026-10-05.

## The target

`mattyv/FlashRadixTree`, a radix tree keyed by strings, with a splay tree variant and a test suite. One translation unit, `main.cpp`, includes it all.

| File | Lines | What it is |
| --- | --- | --- |
| FlashRadixTree.hpp | 1216 | The tree, a class template over key, value, match mode and allocator, with iterators |
| SplayTree.hpp | 825 | The splay tree the node children use |
| Test.hpp | 1210 | The tests, with a throwing allocator |
| main.cpp | 600 | The benchmark driver |

The gate ran as `cplusp gate main.cpp -- -std=c++23 -ffp-contract=off -include functional`. The last flag pre-includes a header the code relies on through another header, which clang 18 with libstdc++ 13 does not provide that way. Without it the gate refuses the file as not compiling, which is right. The code is C++20 and compiles as C++23 unchanged.

The gate reads no markers yet, so every finding counts as a finding in verified code. The split into verified, trusted and plain cannot be measured until the markers are read. That is the next piece the trial asks for.

## The numbers

| File | Lines | Lines with a finding | Findings |
| --- | --- | --- | --- |
| FlashRadixTree.hpp | 1216 | 190 | 248 |
| SplayTree.hpp | 825 | 119 | 161 |
| Test.hpp | 1210 | 257 | 274 |
| main.cpp | 600 | 21 | 26 |
| All | 3851 | 587 | 709 |

The rows, from the most findings down. The first run had 695 findings with a different shape, see the next section.

| Row | Findings | What the lines are |
| --- | --- | --- |
| iostreams | 175 | The tests and the driver print to `std::cout` |
| unlisted | 170 | Template machinery: unresolved constructs and member names in templates, the class's own name inside its template, parameter packs, concepts and requires clauses, friends |
| strings | 72 | Keys are `std::string` |
| metaprogramming | 66 | Dependent names and `typename T::type` in templates |
| iterators | 57 | The API returns iterators, and the tests compare them with `end()` |
| plain_int | 32 | `int` loop counters and `int` values in the tests |
| raw_pointer | 31 | Node pointers in the tree and the iterators |
| operator_overloading | 20 | The iterators' `++`, `--`, `[]` |
| exceptions | 20 | `throw` and `try` in the tests and on allocation failure |
| lvalue_references | 14 | Reference locals and `catch` by reference |
| templates | 8 | Enum template parameters |
| global_state | 8 | The test allocator's static counters, with no `reads` or `modifies` lines |
| the rest | 36 | Pointer arithmetic, function pointers, moves, raw allocation, implicit conversions and single findings |

## What the trial changed in the gate

Three kinds of finding were the gate's fault, not the code's. Each is a row or a pin now.

- **Streams.** The first run reported 169 lines of `std::cout << ...` as two names for one object, because a stream is a mutable global passed by reference. The rule was right and the message was wrong. The row `iostreams` says what the bot needs to hear: a stream is trusted code.
- **A cast nobody wrote.** The alias lines `using tree_pointer = std::conditional_t<constness == ...>` were reported as C-style casts. Clang writes `(Enum)1` for an enum template argument it substitutes. The allowlist no longer judges what sits under a substituted argument, and the templates pair pins it.
- **A reference that reaches nothing.** `return _find(key);` was refused as a reference to a global escaping. Every user call that returns a reference carried the State root. A function that passed the gate returns only what its parameters or `this` reach, so its callers drop that root. Nine findings gone.

## What the trial says about the plan

- **A generic container library is outside the subset as written.** The tree is a template over four parameters, one of them an enum value. It reaches for dependent names, concepts and friends to do it. The row `templates` allows type parameters only. The way in is not to admit all of that. It is to instantiate the tree for the key, value and allocator the program uses. Then the gate and the model run on the instantiation. The model is per type already, decision 0029, so this is the shape the proof wants.
- **Enum template parameters are values.** `MatchMode::Exact` as a template argument is a compile-time value the model can carry as a constant. A row that admits enum and integer template parameters, and refuses type-level computation on them, would take the eight `templates` findings. It would take a share of the unlisted ones too. Not decided here.
- **An iterator API needs a verified face.** `find` returns an iterator and the caller compares it with `end()`. The subset wants an optional or an index. A thin verified layer over the container, with those return types, is the shape the examples already show.
- **Keys as bytes.** Seventy-two findings say `std::string`. Decision 0031 says text is bytes, and a radix tree over `std::span<const uint8_t>` keys is a natural fit. The tree does not need text, it needs ordered bytes.
- **The test allocator's counters are the state the rule is for.** Eight findings name two static counters. Functions change and read them with no line saying so. That is decision 0035 doing its job on code nobody wrote for it.
- **Nothing here decides 0012.** The code has no threads, so the rule on shared variables was not exercised. That trial needs a concurrent target.

## What to do next

1. Read the markers, so the trial can report verified, trusted and plain lines instead of findings.
2. Pick one function of the tree, instantiate it for `std::span<const uint8_t>` keys and `int32_t` values, and take it through the thin slice: gate, model, differential run.
3. Decide on enum template parameters, with a case in the battery.
