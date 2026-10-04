// Model B: the contract requires a non-zero divisor, and a quotient no larger than MAX. The quotient is `fdiv`, and the contract is an error bound.
include "../../Double.dfy"
import opened Double

method ratio(a: real, b: real) returns (result: real)
  requires b != 0.0 && abs(a / b) <= MAX
  ensures abs(result - a / b) <= EPS * abs(a / b) + ETA
{
  RoundError(a / b);
  result := fdiv(a, b);
}
