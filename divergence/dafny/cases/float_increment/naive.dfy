// Model A: a double is a real, and the sum is exact. The proof goes through.
// Above 2^53 the doubles are 2 apart, and the hardware rounds x + 1.0 back to x.
method next(x: real) returns (result: real)
  ensures result == x + 1.0
{
  result := x + 1.0;
}
