// Model B: the same model, now of fixed.cpp. The C++ computes in double, which is the type the model is of.
// So the model is exact for its type, and the bound is true for the C++.
include "../../Double.dfy"
import opened Double

method sum(a: real, b: real) returns (result: real)
  requires abs(a) <= MAX / 4.0 && abs(b) <= MAX / 4.0
  ensures abs(result - (a + b)) <= EPS * abs(a + b) + ETA
{
  RoundError(a + b);
  result := fadd(a, b);
}
