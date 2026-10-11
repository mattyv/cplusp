# 0123: The core scans the companion file

Date: 2026-10-11. Status: decided. Amends 0077, 0080 and 0083.

## Decision

The scan of the companion file moves from the shell into the Verus core. The rules of 0080 and 0083 do not change. The output of the gate and of `prove` does not change.

- The shell gives the core the bytes of the file. The core gives the refusals and the names that the file declares. Each refusal has its line and its kind. A kind that names a word has the span of the word in the bytes. Each declared name is a span of bytes, with its line and a mark for a lemma. The shell makes the sentences, puts them in order and removes the copies, as before.
- The core reads the file in two parts. The lexer reads the bytes as Dafny reads them, and makes a list of tokens. A token is a word with the declaration word before it, or `"`, `@` or `{:`. A comment makes no token. A rule then reads each token.
- The core proves two things. First, the code gives exactly the result of the spec. Second, a file passes only when four things are true. The file holds no byte that 0083 refuses. Each comment ends. No token is a refused keyword, `"`, `@` or `{:`. No declared name is a name of the model.
- The lexer reads the bytes in one loop, so a long file needs no deep stack.

## Why

The scan guards the strongest claim of the tool. A companion file adds Dafny text to the model. If the scan misses a keyword, the file can add an axiom, and `prove` can say `ok: proved` for a false contract. Decision 0077 puts each such decision in the core. The user chose this scan as the first step of the move, because a defect in it does the most harm.
