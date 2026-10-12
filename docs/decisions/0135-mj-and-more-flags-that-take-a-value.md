# 0135: The gate refuses -MJ, and knows more flags that take a value

Date: 2026-10-12. Status: decided. Amends 0128 and 0130.

## Decision

- The gate refuses `-MJ` and `-MJ<file>` with the reason `Reads`. The gate runs the compiler itself, and `-MJ` makes the compiler write a file.
- The list of flags that take a separate value grows. Each one is an exact match. The new flags are these:
  - `-F`, `-L`, `-l`, `-B`, `-z`, `-u`, `-e`, `-T`, `-rpath`, `-arch` and `-dumpdir`.
  - `-Xlinker`, `-Xassembler`, `-Xanalyzer`, `-Xarch_host`, `-Xarch_device` and `-mllvm`.
  - `-iprefix`, `-iwithprefix`, `-iwithprefixbefore`, `-iframework`, `-iwithsysroot`, `-ivfsoverlay` and `-stdlib++-isystem`.
  - `--sysroot`, `-working-directory`, `-module-dependency-dir`, `-resource-dir` and `-fdebug-compilation-dir`.
  - `-serialize-diagnostics`, `--serialize-diagnostics` and `--param`.
  - `--language`, `--output`, `--include-directory`, `--define-macro`, `--undefine-macro`, `--include`, `--imacros`, `--prefix`, `--system-header-prefix` and `--library-directory`. The rules of 0130 and 0134 apply to each one.
- The sentence "With `-E` alone, clang-tidy would judge nothing." leaves docs/policy.md. The review found that clang-tidy still judges with `--preprocess`, the other spelling of `-E`.

## Why

The review of 0134 found that `-- -MJ main.cpp` made clang-tidy write a database entry over `main.cpp` before the gate judged it. The source was gone. A bot that writes `-MJ compile_commands.json`, the usual way to make a database, would lose the database of the project. The gate drops `-MJ` from its own run of the compiler. But it passes the flags to clang-tidy as they are, and clang-tidy runs the driver over them.

The review also tried 95 flags at the end. Each one failed closed, but the flags that the list did not know failed by chance. Some linked the file and wrote `a.out` into the folder of the project. Some wrote a file named `-MM`. The message named the wrong cause.
