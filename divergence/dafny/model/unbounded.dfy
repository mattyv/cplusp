// An operation with no bound on its exact result does not verify, because C++ gives infinity above DBL_MAX, decision 0153.
include "../Double.dfy"
import opened Double

method product(a: real, b: real) returns (result: real)
{
  result := fmul(a, b);
}
