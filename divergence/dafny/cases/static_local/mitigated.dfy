// Model B: a function-local static is a global with a narrow name, so `n` is a field of the State value, decision 0029.
// The method takes the State in and gives it back, and its contract says how `n` changes. A second call sees the value
// the first call left.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype State = State(n: int32)

method counter(s: State) returns (s': State, result: int32)
  requires s.n < 0x7FFF_FFFF
  ensures s'.n as int == s.n as int + 1 && result == s'.n
{
  s' := State(s.n + 1);
  result := s'.n;
}

// The model proves 1 and then 2, as the witness prints.
method Demo() {
  var s := State(0);
  var s1, first := counter(s);
  var s2, second := counter(s1);
  assert first == 1 && second == 2;
}
