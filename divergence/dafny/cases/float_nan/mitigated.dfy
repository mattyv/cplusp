// Model B: the C++ requires finite values and compares the difference against a tolerance that is a double, 2^-30.
// The difference is `fsub`, so it rounds once. The contract has slack for that rounding, and it is a bound, never an equality.
// The model has no NaN, so it is exact for the finite values the C++ requires.
include "../../Float.dfy"
import opened Float

const T: real := 1.0 / 1073741824.0  // 2^-30, a double

method same(a: real, b: real) returns (result: bool)
  requires abs(a) <= MAX / 2.0 && abs(b) <= MAX / 2.0
  ensures result ==> abs(a - b) <= T + 2.0 * EPS * T + 2.0 * ETA
  ensures abs(a - b) <= T - 2.0 * EPS * T - 2.0 * ETA ==> result
{
  var gap := fsub(a, b);
  RoundError(a - b);
  result := gap <= T && -gap <= T;
}
