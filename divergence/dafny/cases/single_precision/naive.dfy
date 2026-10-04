// Model A: the literal model of a double sum. It has one rounding, the rounding of `double`.
// It proves the double bound for a sum the C++ computes in float, where the error is far larger.
include "../../Double.dfy"
import opened Double

method sum(a: real, b: real) returns (result: real)
  requires abs(a) <= MAX / 4.0 && abs(b) <= MAX / 4.0
  ensures abs(result - (a + b)) <= EPS * abs(a + b) + ETA
{
  RoundError(a + b);
  result := fadd(a, b);
}
