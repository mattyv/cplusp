# 0023: The float error axiom carries an absolute term

Date: 2026-10-03. Status: decided. Amends item 1 of decision 0020.

## Decision

The rounding error axiom reads `|round(x) - x| <= eps * |x| + eta`, for every `|x|` up to the largest double. `eps` is 2^-53, the unit round-off, `DBL_EPSILON / 2` in C++. `eta` is 2^-1075, half the smallest subnormal, `DBL_TRUE_MIN / 2` in C++. There is no lower magnitude bound, and no `MIN_NORMAL`. A contract on a float result reads `|result - (a + b)| <= eps * |a + b| + eta`.

## Why

Decision 0020 made the axiom hold in the normal range only, and asked every contract for a lower bound on the result. The float review showed that was the wrong correction. A sum or difference of two doubles below the normal range is exact in hardware, so the bound was never needed there. For a second rounding the operand is an intermediate value that no clause on the inputs can name. So the bound became a clause a bot cannot read, and one case excluded its own witness. Decision 0019 named that as a failure sign.

The absolute term is the textbook model of gradual underflow. It is true for every real up to the largest double under round to nearest even. It needs no clause on the inputs, and every float model verifies against it in under two seconds.

## What changes

`Float.dfy` carries `ETA` and the new axiom, and loses `MIN_NORMAL` and the unused monotonicity axiom. Every float bound gains `+ eta`, or a small multiple for several roundings. The gate also refuses flush-to-zero, x87 arithmetic and the fast float models, because the axiom rests on gradual underflow and one rounding per operation.
