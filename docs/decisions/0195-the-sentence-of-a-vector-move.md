# 0195: The sentence of a vector move

Date: 2026-10-27. Status: decided. Builds on 0171, 0185, 0186 and 0194. Amends the sentence of 0171 and 0186 for a move in a place with no rule. The review of 0194 found that a move of a vector in such a place got the sentence for a unique_ptr.

## Decision

A `std::move(v)` of a vector in a place with no rule has a sentence of its own:

"a std::move of a std::vector has no rule here. It has a rule as the start value of a local vector and in the init list of a constructor. It also has a rule at a parameter by value of a call. That call stands alone, is the value of a return, or is the start value of a local that is no vector."

A move of a `std::unique_ptr` keeps the sentence of 0171.

## Why

The sentence of 0171 names a `std::unique_ptr`, and it says that the start value of a local is a place with a rule. For a vector, neither is true. A call with a move as the start value of a local vector has no rule. The bot reads the sentence and writes the next form from it, so the sentence must name the places that have a rule.

## What changes

The core gives the new refusal for a move of a vector in a place with no rule. The shell prints the sentence. The refuse fixture of 0194 gains three such moves, and a vector by value of a struct that holds a sequence. The loose fixture of 0194 gains a call that stands alone, and a call that moves a unique_ptr and a vector.
