# 0034: The differential run is the first match check

Date: 2026-10-05. Status: decided. Follows 0017, which planned to test a translator by compiling the Dafny and running both sides on the same inputs. There is no translator, so the run tests the hand-written model instead.

## Decision

Every battery case may carry a driver pair, `drive.dfy` and `drive.cpp`, and a `differential` block in `case.yaml` that names the argument types and ranges. The command `divergence differential CASE` generates inputs from the block. The edges of each range come first, and a fixed seed gives the rest. Dafny compiles the mitigated model to a program. The compiler builds the C++ under the rule with the sanitizers. The command runs both on the inputs and compares the lines. One verdict line: `agree` or `diverge`, with the first input that parts them and both outputs. A run it cannot complete is an error, never a verdict. With `--naive` it runs the naive model against the bot's C++ over the whole range of each type. The test requires a divergence wherever the battery says the naive model is wrong.

The thin slice uses the same run as its first match check. It runs the bot's model against the bot's C++ on inputs, before any contract is parsed.

## Why

The battery proves the divergences we thought of. A case is a divergence a person imagined, wrote down and showed with a witness. The run looks for the ones nobody imagined, on hundreds of inputs per case. It is the only check so far that ties the model to the C++ by more than a person's reading. The naive run proves the run can see. A run that misses the fault the witness found proves nothing about the faults it did not find. The aliasing cases show the limit. No input reaches `f(x, x)`, so those cases carry no driver, and the gate is the only check on them.

## What changes

Six cases carry drivers: signed overflow, signed division, shift, sign compare, promotion before widening and the fold. The `divergence` command gains the subcommand. The test `the_model_and_the_cpp_agree_on_every_input_and_the_naive_model_does_not` runs every case that has a driver. The battery README describes the files and the block.
