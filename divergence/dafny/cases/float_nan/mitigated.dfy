// Model B: the C++ requires finite values and compares with `<=` twice. The model has no NaN, so it is exact for finite values.
// The meaning is that of model A, a real comparison. The difference is in the C++, which now says that no NaN comes in.
method same(a: real, b: real) returns (result: bool)
  ensures result == (a == b)
{
  result := a <= b && b <= a;
}
