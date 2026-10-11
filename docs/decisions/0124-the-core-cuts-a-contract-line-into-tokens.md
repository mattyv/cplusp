# 0124: The core cuts a contract line into tokens, and folds the constants

Date: 2026-10-11. Status: decided. Amends 0077, 0082 and 0106.

## Decision

The lexer of a contract line and the fold of named constants and enumerators move from the shell into the Verus core. Each step keeps every test and the output of the gate and of `prove`, with one exception below.

- Step 1: the lexer. The shell gives the core the bytes of the line. The core gives a list of tokens, each with its span in the bytes. A name has a mark when a `(` follows it. A number has its value, or the reason that the core cannot read it. The shell gives each name its id. It keeps the calls to names that the companion file does not declare, and it makes the text of each refusal.
- The core proves two things for step 1. First, the spans are in order. Each byte outside the spans is ASCII white space. That is a space, a tab, a line feed, a carriage return, a vertical tab or a form feed. So the lexer drops no text except white space. Second, the value of a number is the value of its digits in its base, without the separators and the suffix. A number that the core cannot read never becomes a value.
- Step 2: the fold. The shell gives the core the tokens with the ids of their names. It also gives the constants, the enums and the hidden names, each by id. The core gives the tokens after the fold. It proves the rules of 0106 and 0109. A name becomes its value only when it is a constant. No parameter, local or bound name can hide it, and no call or `::` can stand next to it. `A::B` becomes an enumerator only when `A` names one enum of the file, no quantifier binds `A`, and `B` is an enumerator of `A`.
- The exception: white space in a contract is ASCII only. The shell also skipped the other white space of Unicode, such as the no-break space. The core refuses such a character as a character that a contract cannot hold. No example and no test has one.

## Why

The lexer and the fold decide what a contract says. The lexer can drop a character or read a number wrong. The fold can put a value where a parameter hides the constant. Then the prover proves a contract that the author did not write. Decision 0077 puts each such decision in the core, and lists the lexer third. The user chose this move second, after the companion file. A white space that the eye cannot see has no use in a contract, and the core is simpler when it reads only ASCII.
