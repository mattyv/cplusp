# 0083: The companion file is plain text after the methods, and it names nothing of the model

Date: 2026-10-08. Status: decided. Amends 0079 and 0080, from the second review of the check of the companion file.

## Decision

- The companion file holds only printable ASCII, tabs and line feeds. It can also hold a carriage return directly before a line feed. The shell refuses each other character at its line. The sentence is "a character that a companion file cannot hold." Dafny ends a line at a carriage return alone, and the shell did not. So text after `//` and a lone carriage return was a comment for the shell and code for Dafny.
- The companion file may not declare a name that the prelude or the model uses. These names are `Option`, `Some`, `None`, `Vec`, `value` and the integer types. Each name that starts with `v_`, `c_`, `S_`, `f_` or `b_` is also a name of the model. Dafny reads `Some(x)` in a method as a function of the companion before the constructor of `Option`, with no error. So a companion `function Some` changed the meaning of the model.
- The text of the companion file follows the methods in the Dafny file. A comment reaches forward only, so no text of the companion can hide a method.
- The verdict still takes the number of methods, decision 0080, but only as a floor. Dafny counts six items of the prelude, so the count alone cannot see a hidden method. When the count is the only fault, `prove` says so in one line.
- The shell reads a parse error on a line of the companion file as it reads a resolution error, decision 0080. It prints at its line as `Dafny says:` and the message, with exit 1. A parse error on a line of the model stays a failure of the tool.

## Why

The second review found two companion files that made a wrong body prove: a lone carriage return, and a function named `Some`. It also found that the count of verified items includes the prelude. Each fix removes a difference between what the shell reads and what Dafny reads, or a place where the author's text meets the model's names.
