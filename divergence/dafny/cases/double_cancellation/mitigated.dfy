// Model B: two roundings, so two error terms. The bound comes from the magnitudes of the operands, not from the result.
// Each rounding adds ETA, and the second rounding is of s - b, where s is the rounded sum. The bound carries 3 * ETA.
include "../../Double.dfy"
import opened Double

method shifted(a: real, b: real) returns (result: real)
  requires abs(a) <= 1.0 && abs(b) <= 1.0
  ensures abs(result - a) <= 4.0 * EPS * (abs(a) + abs(b)) + 3.0 * ETA
{
  var s := fadd(a, b);
  RoundError(a + b);
  result := fsub(s, b);
  RoundError(s - b);
}
