// Model A: a double is a real, and the product is exact. The proof goes through.
// The hardware rounds the product, and 1e-400 is below the smallest subnormal, so `scaled(1e-200, 1e-200)` is 0.
method scaled(a: real, b: real) returns (result: real)
  ensures result == a * b
{
  result := a * b;
}
