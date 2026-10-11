# 0126: The sentence names each invisible character by its code

Date: 2026-10-11. Status: decided. Amends 0125.

## Decision

The core can refuse a character in a contract. The sentence then names it by its code point, as `U+200B`. A letter, a digit or a visible ASCII character is the exception. It stays in quotes, as `'$'` or `'é'`.

## Why

Decision 0125 named white space and control characters by their code points. The review found that a format character is neither. A zero-width space or a right-to-left override then printed between quotes with nothing visible. The bot cannot see the defect, which is what 0125 set out to stop. A letter, a digit and a visible ASCII character are the only ones that the eye can read in quotes.
