# 0016: One generic clang-tidy check driven by matcher patterns in the policy

Date: 2026-10-03. Status: decided.

## Decision

The clang-tidy plugin has one generic check, `cplusp-matcher`. It reads clang AST matcher patterns as text from its options and reports each match with the rule id as the message. The patterns live in the policy file, in a `detect` entry of the form `matcher: "enumDecl(unless(isScoped()))"`. Eighteen rules use them. The rules that need real code keep a hand-written check: `mutable`, recursion, lambda limits, impure operators, multiple inheritance, unlisted state, and the function index with its markers.

## Why

A clang-tidy check must be C++. Formal verification cannot reach it, and the part that can be wrong is the pattern against clang's model of C++, whatever language sits behind it. So the C++ must be as small as possible. clang compiles matcher patterns from text at run time, as `clang-query` does. One generic check turns most rules into one line of policy each, and adding a rule stops needing C++ at all.

## What changes

A `clang-tidy/` directory with the plugin, built with CMake against LLVM 18. The `matcher` form of `detect`. The gate's `--plugin` option. The plugin is the second trusted edge: C++, tested by the sample pairs, listed in CLAUDE.md.
