// Model B: the C++ requires finite values and compares the difference against a tolerance. The model has no NaN, so it is exact for finite values.
// The meaning is a real comparison, as in model A. The difference is in the C++, which now says that no NaN comes in and which tolerance it means.
include "../../Float.dfy"
import opened Float

method same(a: real, b: real) returns (result: bool)
  ensures result == (abs(a - b) <= 0.000000001)
{
  var gap := a - b;
  result := gap <= 0.000000001 && -gap <= 0.000000001;
}
