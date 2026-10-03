// Model A: `total` is a field of a State object, and `add` is a bodyless axiom method with the contract of the C++.
// The contract has no `modifies`, so Dafny lets the caller assume that `total` does not change. `delta` proves 0.
// The C++ function changes `total`, and `delta()` returns 1.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class State {
  var total: int32
}

method {:axiom} add(s: State, x: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  requires -0x4000_0000 <= s.total < 0x4000_0000
  ensures s.total as int == old(s.total) as int + x as int

method delta(s: State) returns (result: int32)
  requires -0x4000_0000 <= s.total < 0x4000_0000
  ensures result == 0
{
  var before := s.total;
  add(s, 1);
  result := s.total - before;
}
