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

In the first two runs the gate read no markers, so every finding counted as a finding in verified code. The third run reads them, see the section on it below.

## The numbers

| File | Lines | Lines with a finding | Findings |
| --- | --- | --- | --- |
| FlashRadixTree.hpp | 1216 | 177 | 226 |
| SplayTree.hpp | 825 | 117 | 143 |
| Test.hpp | 1210 | 256 | 273 |
| main.cpp | 600 | 21 | 27 |
| All | 3851 | 571 | 669 |

The rows, from the most findings down. The first run had 695 findings with a different shape, see the next section. These are the numbers after the night's fixes.

| Row | Findings | What the lines are |
| --- | --- | --- |
| iostreams | 175 | The tests and the driver print to `std::cout` |
| unlisted | 123 | Template machinery: unresolved constructs and member names in templates, parameter packs, concepts and requires clauses, friends |
| strings | 72 | Keys are `std::string` |
| metaprogramming | 66 | Dependent names and `typename T::type` in templates |
| iterators | 57 | The API returns iterators, and the tests compare them with `end()` |
| plain_int | 32 | `int` loop counters and `int` values in the tests |
| raw_pointer | 31 | Node pointers in the tree and the iterators |
| operator_overloading | 20 | The iterators' `++`, `--`, `[]` |
| exceptions | 20 | `throw` and `try` in the tests and on allocation failure |
| lvalue_references | 14 | Reference locals and `catch` by reference |
| templates | 8 | Enum template parameters |
| global_state | 8 | The test allocator's static counters, with no `reads` or `modifies` lines, and `std::stoi` in the driver, which reaches `errno` |
| builtins | 2 | `__builtin_expect` in the splay tree |
| the rest | 41 | Pointer arithmetic, function pointers, moves, raw allocation, implicit conversions, two aliasing and two `unique_ptr` findings, and single findings |

The table is from a second run, under decision 0037, where the state check reads the code the compiler generates. The first run gave 664 findings on 569 lines. The second gives five more and loses one. Lost: a write to a static counter in a template body that nothing instantiates. It has no generated code, so the translation unit that instantiates it will judge it. Gained: `std::stoi` in the driver, which reaches `errno` through a reference the gate cannot follow. A call through a table of pointers to member functions in the splay tree, which the row `function_pointers` now sees as a deduced type. Four findings of the rows `aliasing` and `unique_ptr` from the round of decision 0033. The eight state findings are otherwise the same lines.

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

## The third run, with markers

On 2026-10-07, under decisions 0039 and 0047 to 0050. A scratch copy marks each function of Test.hpp and main.cpp plain, eleven functions in all. `RunTests` is one function of about 1165 lines. Most of the driver is under `#ifdef __APPLE__`, so the compiler does not see it on this host. The two headers of the tree carry no marker. The flags are those of the first run.

With no marker the gate now gives 868 findings, not 669. The rise is in the row `function_pointers`, from 4 to 203, under decisions 0048 to 0050. Of these, 165 are `std::endl`: a function passed by name to `operator<<`, which calls through it. In the tree, 21 come from `make_unique_alloc`, which gives each node a `std::unique_ptr` with a `std::function` deleter. Each release of a node is a call through that deleter.

| File | No marker | Tests and driver plain |
| --- | --- | --- |
| FlashRadixTree.hpp | 251 | 254 |
| SplayTree.hpp | 143 | 143 |
| Test.hpp | 440 | 3 |
| main.cpp | 34 | 3 |
| All | 868 | 403 |

What the markers show:

- **The tests and the driver go out of view.** 468 findings go, and none of them is in the tree.
- **A type of the test code stays verified.** Six findings stay in the plain files. Each is a declaration outside a function: the static counters of the test allocator, and the fields of the driver's `Data`. A marker takes only a function, decision 0039. This trial does not decide whether a type can take one.
- **The tree runs the test allocator.** Three findings are new. `verified code calls ThrowingAllocationAllocator::allocate, which is plain`, and the same for `deallocate` and the constructor. The tests instantiate the tree with the allocator that throws, so the tree runs plain code. That is decision 0047 at work on code that nobody wrote for it. The allocator needs a contract and a trusted mark, or the verified build uses `std::allocator`.
- **The tree's own findings stay.** The two headers have 397. The largest rows are unlisted 121, metaprogramming 66, strings 42 and raw_pointer 31. Then function_pointers 29, operator_overloading 19, plain_int 11 and exceptions 11. Then iostreams 10, lvalue_references 10, templates 8 and iterators 8. The rest is 31 in thirteen rows. This is the work for a bot, or the share of the tree to mark trusted.

## The thin slice: radix_find

On 2026-10-07. The tree itself cannot take byte keys: a concept refuses `std::span`, and its find uses rows that the gate refuses. So the slice is a new find in the subset, with the shape of the tree's exact find. It is the battery case `radix_find`. A node holds a byte prefix, an optional value and a vector of children, and the find recurses with a span of the key.

- **The gate** passes the find as written.
- **The model** proves that the find gives a value exactly when the tree stores the key with that value. The tree must be well formed and at most 1000 high.
- **The differential run** agrees with the C++ on 200 keys over three bytes.
- **FlashRadixTree as the oracle.** A program outside this repo puts the same five keys in the real tree. It asks both finds for every key of length 0 to 6 over three letters, 1093 keys in all. They differ on one: `"ab"`. The real tree gives 2, the value of `"abaab"`, and the verified find gives none.

The cause is in `_findExact`. When the key ends at a node with no value, the loop does not stop. It looks again below that node with the same key, and it stops at the first node whose prefix is the rest of the key. An `else return nullptr;` after the test `key.size() > (seen += ...)` stops it. The tree is GPL-3.0, so this repo holds no copy of it, and the comparison is not part of the battery.

## What to do next

1. Fix `_findExact` in FlashRadixTree, and take the next function through the slice: `insert`, with a model of the contents the tree stores.
2. Enum template parameters wait for a verified function that needs one. The exact find has no match mode.
3. Give the node a deleter type with no state, so that each release is a direct call. Or mark `make_unique_alloc` trusted, with the deleter inside it.
4. A type of test code takes a plain marker, decision 0051. Mark the test allocator and the driver's `Data` plain, and run the trial again.
