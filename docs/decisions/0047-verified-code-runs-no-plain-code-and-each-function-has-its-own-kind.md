# 0047: Verified code runs no plain code, and each function has its own kind

Date: 2026-10-07. Status: decided. Amends 0039: its rule on a reference to a plain function, and what a kind covers.

## Decision

- **Each function has its own kind.** A function takes the kind of the markers written on its own declarations. A lambda, a member of a local class and an explicit specialization are functions of their own. With no marker written on them, they are verified, also inside a trusted or plain body. Each function that the file writes reports its place, so a finding takes the kind of the innermost function that holds it.
- **A marked function stays in its file.** The gate refuses one with its first or last token in a macro or another file. Its region could hold code that is not its own.
- **Each build is its own run.** The gate runs clang-tidy once for each file and its flags. The places of one run judge only the findings of that run. Two builds can read one header, with a marker in one build and no marker in the other.
- **Verified code runs no plain code.** The gate reads the calls from the compiler's lowered form, decision 0037. A call from a verified function counts when it reaches a plain function. It can reach it directly, or through code that the file does not write, such as the library and the members that the compiler writes. The gate refuses the call at its line. A name of a plain function that never runs is no call. This replaces the reference rule of 0039.
- **A plain override is refused.** The gate refuses a plain function that overrides a function that is not plain. A verified call of the base can run it. The lowered form holds the override only when the file uses the derived class.

## Why

The review of the 0039 green step found six ways past it. A destructor runs where no call names it. The library calls an operator that the file wrote. A virtual call reaches an override. Each of these runs plain code from verified code and names nothing. What runs counts, decision 0038, and the lowered form lists what runs. A list of the ways to call without a name would grow with each review.

A local class and a lambda in a trusted body took the trusted kind. So did an explicit specialization with no marker. A macro at the end of a trusted body put a verified function in the trusted region. Two builds of one header shared one list of regions. Each of these loosened code that has no marker of its own.

## What changes

The plugin reports a place for every function that the file writes. The gate runs once for each build and asks the core the kind of each finding's place. The plugin reports a call that reaches plain code at its place. The gate keeps it when the core gives that place the verified kind. The check of references in the tree goes. `cplusp:assume` on a function gets its own message, because it waits. Three fixtures, and two more lines in the fixture of marker errors.
