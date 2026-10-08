# 0067: A sequence stays constant across a call because the gate passed the file, and a bound name is an integer

Date: 2026-10-08. Status: decided. Amends 0058 on what a method with no body can do, and 0064 on the type of a bound name.

## Decision

- The model reads a sequence parameter as one value for the whole call. That holds only when no callee writes the data that the sequence views. A full method writes no global, because the translator has no rule for a write to one. A method with no body can hide such a write.
- So the model rests on two rules outside it. The gate's row `global_state` demands a `modifies` line on each function that writes a global, and on each caller. The translator refuses each `modifies` line, because it has no rule for one yet. Together they refuse every file in which a callee writes the data behind a sequence.
- So `cplusp model` alone does not keep the sentence of 0058 that no caller proves more than the code gives. Only `cplusp gate` and `cplusp model` together keep it. The command of the next slice that runs the prover runs the gate first.
- The core refuses such a call itself in a later slice, when a call can depend on the model of its callee.
- A name that `forall` binds is an exact integer, and the model prints its type, `forall j: int`. Without the type, Dafny guessed it from the body, refused a file in which the body did not use it, and read `forall j :: j` as a bool.

## Why

The review of slice 4 found a span of const over a global that a callee changes. The callee had no model, so its method had no body. Dafny then read the span as the same value before and after the call, and proved a false contract. The gate refused the same file, at the write and at the global. No decision said so. The same review found the untyped bound name.

## What changes

A test pins the reliance: the gate refuses the file at the write, and the translator refuses the callee. The shell prints `forall b_j: int`. No rule of the core changes.
