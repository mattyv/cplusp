// Model B: a double is a real after rounding. The sum is `fadd`, and the contract is an error bound, never an equality.
// The magnitude bounds keep the sum below MAX, where the rounding error bound holds and the hardware gives no infinity.
// The lower bound keeps a nonzero sum out of the subnormal range, where the error bound does not hold.
include "../../Float.dfy"
import opened Float

method sum(a: real, b: real) returns (result: real)
  requires abs(a) <= MAX / 4.0 && abs(b) <= MAX / 4.0
  requires a + b == 0.0 || MIN_NORMAL <= abs(a + b)
  ensures abs(result - (a + b)) <= EPS * abs(a + b)
{
  RoundError(a + b);
  result := fadd(a, b);
}
