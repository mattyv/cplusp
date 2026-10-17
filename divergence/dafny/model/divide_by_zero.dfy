// A division that may divide by zero does not verify, decision 0153.
include "../Double.dfy"
import opened Double

method ratio(a: real, b: real) returns (result: real)
  requires abs(a) <= 1.0 && abs(b) <= 1.0
{
  result := fdiv(a, b);
}
