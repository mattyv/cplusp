# 0039: The gate reads the markers

Date: 2026-10-07. Status: decided. Builds the markers of decision 0003 and of the plan's section on markers. Settles the gate's part of the open item `-markers`.

## Decision

The plugin reads the markers of `include/cplusp.h` from the compiler's tree, where `[[clang::annotate]]` keeps them with their reasons. A function takes the kind its marker names, on any of its declarations. A function with no marker is verified.

- **What a kind covers.** A trusted function's body is trusted: its constructor initializers and its block. Its declaration stays verified, because verified callers read it. A plain function is plain from its first token to its last, on every declaration. Code in no function is verified. A finding takes the kind of the innermost function that holds it.
- **What a kind keeps.** The verified core decides, as it has since the first build. In verified code every finding stands. In trusted code a finding of a Trusted only row goes, and every other finding stands. In plain code no finding of a row stands. A finding the gate makes itself, a NOLINT, a pragma or a line directive, stands everywhere.
- **The rules of the markers.** The gate refuses each of these, under the name `marker`. A trusted function with no contract, because its callers rest on the contract alone. A trusted or plain marker with no reason. A function with two kinds. A `cplusp:` annotation that is no marker. A marker on something that is not a function. A reference to a plain function from verified code, because verified code calls only what has a contract.

`CPLUSP_ASSUME` marks one statement, and it waits until a case needs it. The counts of verified, trusted and plain functions wait for the CI report, which is where the plan puts them. A new function is verified by default, and an edited function keeps its kind. The gate does not yet know which functions a change touches, so every unmarked function counts as new.

## Why

Until now every finding counted as a finding in verified code. A trusted body that uses `new` was refused, though the row says trusted code may. The trial on the radix tree could not split its findings. Some a bot must fix, and some sit in code the bot may leave plain. The core has decided what each kind keeps since the first build, and the plugin has kept the markers in the tree since then. The one missing piece was the place of each function.

## What changes

A plugin check that reports the place and kind of each marked function, and the findings above. The core gains the function that gives the kind at a place, with its proof. The gate gives each finding the kind of its place and asks the core whether it stands. A test with fixtures for each rule.
