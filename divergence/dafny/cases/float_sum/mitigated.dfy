// Model B: a double is a real after rounding. The sum is `fadd`, and the contract is an error bound, never an equality.
// The magnitude bounds keep the sum below MAX, where the rounding error bound holds and the hardware gives no infinity.
// The bound has no lower limit. The ETA term carries a sum in the subnormal range.
include "../../Float.dfy"
import opened Float

method sum(a: real, b: real) returns (result: real)
  requires abs(a) <= MAX / 4.0 && abs(b) <= MAX / 4.0
  ensures abs(result - (a + b)) <= EPS * abs(a + b) + ETA
{
  RoundError(a + b);
  result := fadd(a, b);
}
