// Model A: a double is a real, and `==` is the equality of reals. The proof goes through.
// A real has no NaN, so the model is true for every pair of values, and the C++ is false for NaN == NaN.
method same(a: real, b: real) returns (result: bool)
  ensures result == (a == b)
{
  result := a == b;
}
