// A double is a real after rounding, from Double.dfy. The product is fmul, and RoundError gives the one-rounding bound.
// The model has no NaN, so std::isfinite has no clause here. The difference in `near` is fsub, and it rounds once.
include "../../divergence/dafny/Double.dfy"
import opened Double

method product(a: real, b: real) returns (result: real)
  requires abs(a * b) <= MAX
  ensures abs(result - a * b) <= EPS * abs(a * b) + ETA
{
  RoundError(a * b);
  result := fmul(a, b);
}

const T: real := 1.0 / 1073741824.0  // 2^-30, a double

method near(a: real, b: real) returns (result: bool)
  requires abs(a) <= MAX / 2.0 && abs(b) <= MAX / 2.0
  ensures result ==> abs(a - b) <= T + 2.0 * EPS * T + 2.0 * ETA
  ensures abs(a - b) <= T - 2.0 * EPS * T - 2.0 * ETA ==> result
{
  var gap := fsub(a, b);
  RoundError(a - b);
  result := gap <= T && -gap <= T;
}
