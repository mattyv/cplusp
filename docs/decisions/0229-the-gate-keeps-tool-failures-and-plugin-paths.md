# 0229: The gate keeps tool failures and plugin paths

The gate accepts exit 0 from clang-tidy. Exit 1 needs exported diagnostics,
because warnings treated as errors include the marker records that the gate
uses to classify functions. A signal or any other exit code is a tool failure.
Exported diagnostics do not make such a run complete.

The gate resolves a relative plugin path against its initial working directory.
It uses that path both to list checks and to judge each compilation database
entry. The directory of an entry must not change which plugin the gate loads.

The regression tests run a compiler wrapper that exports diagnostics and then
exits with code 42 or a signal. Both runs must fail. Another test loads a relative
plugin path while a database entry uses a different working directory.

Validation in this editing environment is incomplete. Cargo, Clang and Dafny
are unavailable. The regression tests must run in the project toolchain before
these changes can be reported as passing.
