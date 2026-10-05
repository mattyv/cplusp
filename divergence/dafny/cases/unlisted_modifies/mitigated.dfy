// Model B: a global is a field of the State value, decision 0029. `add` takes the State in and gives it back, so the caller knows
// that `total` may change, and the ensures says how. In the C++ contract that is `modifies total`.
// `delta` proves 1. A model of `add` that returns no State is no longer the model of the C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype State = State(total: int32)

method {:axiom} add(s: State, x: int32) returns (s': State)
  requires -0x4000_0000 <= x < 0x4000_0000
  requires -0x4000_0000 <= s.total < 0x4000_0000
  ensures s'.total as int == s.total as int + x as int

method delta(s: State) returns (s': State, result: int32)
  requires -0x4000_0000 <= s.total < 0x4000_0000
  ensures result == 1
{
  var before := s.total;
  s' := add(s, 1);
  result := s'.total - before;
}
