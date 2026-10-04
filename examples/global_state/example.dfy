// A global is a field of one state object, and every function takes the state. `modifies s` is the C++ `modifies total`, and a
// function that only reads has `reads s`. Dafny refuses a body that changes a field outside its modifies clause.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class State {
  var total: int32
}

method add(s: State, x: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  requires -0x4000_0000 <= s.total < 0x4000_0000
  modifies s
  ensures s.total as int == old(s.total) as int + x as int
{
  s.total := s.total + x;
}

function current(s: State): int32
  reads s
{
  s.total
}

method add_twice(s: State, x: int32)
  requires -0x2000_0000 <= x < 0x2000_0000
  requires -0x2000_0000 <= s.total < 0x2000_0000
  modifies s
  ensures s.total as int == old(s.total) as int + 2 * (x as int)
{
  add(s, x);
  add(s, x);
}
