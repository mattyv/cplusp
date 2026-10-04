// Model B: the model of fixed.cpp, which divides by `10.0`. `10.0` is exactly a double, so the one rounding of the division
// is the only rounding, and the bound is true.
include "../../Double.dfy"
import opened Double

method tenth(a: real) returns (result: real)
  requires abs(a) <= MAX / 4.0
  ensures abs(result - a / 10.0) <= EPS * abs(a / 10.0) + ETA
{
  RoundError(a / 10.0);
  result := fdiv(a, 10.0);
}
