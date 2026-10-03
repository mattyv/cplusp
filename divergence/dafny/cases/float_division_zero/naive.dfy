// Model A: a double is a real, and `/` is the division of reals. Dafny asks for `b != 0.0` and fails.
// The model is stricter than the C++ reading of IEEE 754, which gives infinity. C++ calls it undefined.
method ratio(a: real, b: real) returns (result: real)
  ensures result == a / b
{
  result := a / b;
}
