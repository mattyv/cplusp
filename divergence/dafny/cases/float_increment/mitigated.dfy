// Model B: the sum is `fadd`, and the contract is an error bound. The model can neither prove nor refute `result == x + 1.0`.
// At 2^53 the bound EPS * abs(x + 1.0) is about 1.0. Above it the model promises nothing about the last digit.
include "../../Float.dfy"
import opened Float

method next(x: real) returns (result: real)
  requires abs(x) <= MAX / 2.0
  ensures abs(result - (x + 1.0)) <= EPS * abs(x + 1.0) + ETA
{
  RoundError(x + 1.0);
  result := fadd(x, 1.0);
}
