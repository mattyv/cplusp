// Model A: the conversion is `n as real`, which is exact. The proof goes through.
// Above 2^53 an integer is not always a double, and the conversion picks a neighbour.
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method widen(n: int64) returns (result: real)
  ensures result == n as real
{
  result := n as real;
}
