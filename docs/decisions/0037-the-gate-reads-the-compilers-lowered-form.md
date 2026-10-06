# 0037: The gate reads the compiler's lowered form

Date: 2026-10-06. Status: decided. Amends 0035, which said how the state check reads a function. Amends 0036, which gave the gate its own run of the raw lexer. Follows a third inside review of the round, which found fourteen more holes.

## Decision

The state check judges a function on the code the compiler generates for it, not on the source tree. Clang lowers every function to LLVM IR before it emits machine code. In that form there is no implicit code. A destructor at the end of a scope is a call. A copy is a call. A lambda is a function, and the std algorithm that takes it calls it. A template body exists only where it is instantiated. A write to a global is a store to a named global. The plugin asks clang for that form of the translation unit it has already parsed, and reads it with four rules.

- **Stores and loads.** A store to a global is a write. A load from one is a read. Each must be on the function's lines, as decision 0035 says. The gate refuses a store through a pointer it cannot trace to a global, a local or a parameter.
- **Calls.** A call brings its callee's lines. A callee with a body and no lines of its own brings what its body does, found the same way. That covers a std template, a lambda and a constructor the compiler wrote. A callee with no body here brings nothing when a system header declares it. It is a trusted edge. Anywhere else it must have contract lines, or the gate refuses the call, decision 0036. The namespace does not decide. The location does.
- **Arguments.** An argument that is a global is a write or a read of it. The parameter's type decides. It does so for an explicit call today. A non-const reference, pointer or span writes. Anything else reads.
- **Overrides.** An override lists no more than the function it overrides. So a call through a base class brings the base's lines. They hold for every override. The gate refuses a call through a pointer that is no virtual call.

The sequencing check of decision 0026 asks the same table whether a call changes a global, an operator call too. The same principle covers the line directives. The plugin reads them from the preprocessor as it runs under the build's own flags. The gate's own run of the raw lexer goes.

## Why

The third inside review found fourteen ways past the state check and the directive scanner. Eleven had one shape: code that the compiler runs for the author, and that the check had to find for itself. A copy assignment inside a std container. A lambda inside `count_if`. An override behind a base class. An operator with a callee the check did not read. Each needed a walk of its own. Each walk had edges. The walks were half the check. The compiler does this work once, for the build, and after it nothing is implicit. A dozen instruction kinds hold everything a function does. Reading that form deletes the walks and the class of hole they guarded. The three directive holes had the same shape. A second reader of the source ran under flags of its own, which the first reader did not share. There is one reader now, the compiler's, and the plugin asks it.

The alternative was a rule: a destructor, a copy, a virtual function or a lambda may not change a global. It would have deleted the same walks, and it would have cost the RAII examples. The lowered form keeps them. What the compiler runs, the gate sees.

## What changes

Six walks go. They went over destructors, implicit constructors, default member initializers, lambdas, std templates over user classes and the call graph. The plugin generates the lowered form of the translation unit at the end of it and judges every function from that. A finding sits on the line the compiler gives the instruction. The gate reports a destructor that runs at the end of a scope at the brace that ends it. The sequencing check reads a call's effect from the same table. So a lambda inside a std call counts as a change, and so does an operator with a `modifies` line. The allowlist refuses `__restrict` on a member function. The gate's raw-lexer run and its token reader go, and the plugin reports every `#line` and every line marker from the preprocessor's callbacks. The soundness map says that the state check reads the lowered form, and where that form stops. A template that nothing instantiates has none, so the translation unit that instantiates it judges it. A dynamic initializer is the business of the row `global_constructors`. The gate reads a declaration with any `//@` line and no body as its author's claim.
