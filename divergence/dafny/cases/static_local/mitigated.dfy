// Model B: a function-local static is a global with a narrow name, so `n` is a field of the state object.
// The method lists `modifies s`, and its contract says how `n` changes. A second call sees the value the first call left.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class State {
  var n: int32
}

method counter(s: State) returns (result: int32)
  requires s.n < 0x7FFF_FFFF
  modifies s
  ensures s.n as int == old(s.n) as int + 1 && result == s.n
{
  s.n := s.n + 1;
  result := s.n;
}
