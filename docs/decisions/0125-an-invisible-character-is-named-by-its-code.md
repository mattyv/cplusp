# 0125: The sentence names an invisible character by its code

Date: 2026-10-11. Status: decided. Amends 0057 and 0124.

## Decision

- The core can refuse a character in a contract that is white space or a control character. Then the sentence names it by its code point, as `U+00A0`. Every other character stays in quotes, as `'$'`.
- Decision 0124 also amends 0057. Decision 0057 says that the shell cuts each `//@` line into tokens. Since 0124, the core does this.

## Why

Decision 0124 refuses a no-break space in a contract. The review found that the sentence then printed `' ' in a contract`, and a bot reads that as a plain space. It cannot see the defect, so it cannot fix the line. The code point names the character exactly. The review also found that 0124 contradicts 0057 and does not list it. A decision file does not change after it lands, so this file records the amendment.
