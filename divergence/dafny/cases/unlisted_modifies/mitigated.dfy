// Model B: `add` lists `modifies s`, so the caller knows that `total` may change, and the ensures says how.
// `delta` proves 1. Delete `modifies s` and the proof of `result == 1` is no longer the model of the C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class State {
  var total: int32
}

method {:axiom} add(s: State, x: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  modifies s
  ensures s.total as int == old(s.total) as int + x as int

method delta(s: State) returns (result: int32)
  modifies s
  ensures result == 1
{
  var before := s.total;
  add(s, 1);
  result := s.total - before;
}
