# 0134: A flag at the end that takes a value is refused

Date: 2026-10-12. Status: decided. Amends 0130.

## Decision

- The gate refuses a flag that takes a separate value when it is the last flag after `--`. The reason is `Swallows`, as in 0130. The list of such flags is the list of 0130.
- The gate adds its own flags after the flags of the user. So a flag at the end takes the first flag of the gate as its value.

## Why

The coder found it in the green step of the review of 0130. `-I` at the end takes the `-MM` of the gate as its value. The compiler then compiles and links the file in place of a list of its headers. Each run that we tried failed closed, with a link error or a missing file. But it failed by chance, and the message named the link and not the flag. Decision 0130 kept a flag at the end, because nothing came after it in the flags of the user. That was wrong, because the gate adds flags after it.
