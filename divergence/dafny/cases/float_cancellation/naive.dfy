// Model A: a double is a real, and every operation is exact. The proof goes through.
// The hardware rounds the sum, and for a below the unit round-off of b the difference is 0, not a.
method shifted(a: real, b: real) returns (result: real)
  ensures result == a
{
  var s := a + b;
  result := s - b;
}
