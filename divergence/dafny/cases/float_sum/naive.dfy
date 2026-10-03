// Model A: a double is a real, and the sum is exact. The proof goes through.
// The hardware rounds the sum, so `sum(0.1, 0.2) == 0.3` is false for the C++ and true for this model.
method sum(a: real, b: real) returns (result: real)
  ensures result == a + b
{
  result := a + b;
}
