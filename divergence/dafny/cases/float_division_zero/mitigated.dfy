// Model B: the contract requires a non-zero divisor, and a quotient that is zero or in the normal range. The quotient is `fdiv`, and the contract is an error bound.
include "../../Float.dfy"
import opened Float

method ratio(a: real, b: real) returns (result: real)
  requires b != 0.0
  requires a == 0.0 || MIN_NORMAL <= abs(a / b) <= MAX
  ensures abs(result - a / b) <= EPS * abs(a / b)
{
  RoundError(a / b);
  result := fdiv(a, b);
}
