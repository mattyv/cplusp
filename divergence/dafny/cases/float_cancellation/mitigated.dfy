// Model B: two roundings, so two error terms. The bound comes from the magnitudes of the operands, not from the result.
// The second rounding is of s - b, where s is the rounded sum, so the contract cannot name it. A lower bound on a does it:
// s - b differs from a by at most 2 * EPS, so it is at least 2 * EPS, far above the subnormal range.
// The lower bound on a + b keeps the first rounding out of the subnormal range.
include "../../Float.dfy"
import opened Float

method shifted(a: real, b: real) returns (result: real)
  requires abs(a) <= 1.0 && abs(b) <= 1.0
  requires 4.0 * EPS <= abs(a)
  requires a + b == 0.0 || MIN_NORMAL <= abs(a + b)
  ensures abs(result - a) <= 4.0 * EPS * (abs(a) + abs(b))
{
  var s := fadd(a, b);
  RoundError(a + b);
  result := fsub(s, b);
  RoundError(s - b);
}
