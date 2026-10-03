// Model A: the loop carried over. It counts on `n - 1` and `i - 1` wrapping below zero, and Dafny does not wrap.
// The model refuses code that is fine in C++. It is stricter than C++, never looser.
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method count_down(n: uint64) returns (result: uint64)
  ensures result == n
{
  var steps: uint64 := 0;
  var i: uint64 := n - 1;
  while i < n
    decreases i
  {
    steps := steps + 1;
    i := i - 1;
  }
  result := steps;
}
