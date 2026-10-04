// Two operations, two roundings. The model has fmul for the product and fadd for the sum. Each has one RoundError call, on
// the exact value that it rounds. The bound comes from the magnitudes of the operands, not from the result.
include "../../divergence/dafny/Double.dfy"
import opened Double

method multiply_add(a: real, b: real, c: real) returns (result: real)
  requires abs(a * b) <= MAX / 4.0 && abs(c) <= MAX / 4.0
  ensures abs(result - (a * b + c)) <= 3.0 * EPS * (abs(a * b) + abs(c)) + 3.0 * ETA
{
  var p := fmul(a, b);
  RoundError(a * b);
  result := fadd(p, c);
  RoundError(p + c);
}
