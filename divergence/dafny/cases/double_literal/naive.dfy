// Model A: the literal model. It reads `0.1` as the real one tenth, so the product rounds once. The proof goes through.
// The compiler rounds `0.1` to the nearest double first, and the product rounds again, so the C++ misses the bound.
include "../../Double.dfy"
import opened Double

method tenth(a: real) returns (result: real)
  requires abs(a) <= MAX / 4.0
  ensures abs(result - a * 0.1) <= EPS * abs(a * 0.1) + ETA
{
  RoundError(a * 0.1);
  result := fmul(a, 0.1);
}
