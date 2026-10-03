// Model B: the loop counts down to zero and never goes below it. The C++ is rewritten the same way:
// `for (size_t i = n; i > 0; --i)`.
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method count_down(n: uint64) returns (result: uint64)
  ensures result == n
{
  var steps: uint64 := 0;
  var i: uint64 := n;
  while i > 0
    invariant steps as int + i as int == n as int
    decreases i
  {
    steps := steps + 1;
    i := i - 1;
  }
  result := steps;
}
