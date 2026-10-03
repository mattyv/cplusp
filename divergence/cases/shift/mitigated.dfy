// Model B: the same bit-vectors, and the contract stops one short of the width.
method shl(x: bv32, n: bv32) returns (result: bv32)
  requires n < 32
  ensures result == x << n
{
  result := x << n;
}
