// The globals are one State value, decision 0029, and every function that touches them takes it in. A function that changes a
// global gives the State back, as the C++ lists it in `modifies`. A function that only looks at it takes the State and returns no
// State. A caller then knows what a call can change. A static data member is one more field of the same value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype State = State(total: int32, last_id: int32)

method add(s: State, x: int32) returns (s': State)
  requires -0x4000_0000 <= x < 0x4000_0000
  requires -0x4000_0000 <= s.total < 0x4000_0000
  ensures s'.total as int == s.total as int + x as int
{
  s' := s.(total := s.total + x);
}

function current(s: State): int32
{
  s.total
}

method add_twice(s: State, x: int32) returns (s': State)
  requires -0x2000_0000 <= x < 0x2000_0000
  requires -0x2000_0000 <= s.total < 0x2000_0000
  ensures s'.total as int == s.total as int + 2 * (x as int)
{
  s' := add(s, x);
  s' := add(s', x);
}

method next_id(s: State) returns (s': State, result: int32)
  requires s.last_id < 0x7FFF_FFFF
  ensures s'.last_id == s.last_id + 1
  ensures result == s'.last_id
{
  s' := s.(last_id := s.last_id + 1);
  result := s'.last_id;
}
