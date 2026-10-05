// A class is a datatype, decision 0029. The invariant is a predicate over the value, a const method is a function, and a
// method that changes the object takes it in and gives it back. The model has no destructor, so the function that owns
// the guard calls Destroy where the block ends, and the global pool is a State value every function takes and returns.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Counter = Counter(n: int32)

predicate Valid(c: Counter) { 0 <= c.n <= 1000 }

function value(c: Counter): int32 { c.n }

method MakeCounter(start: int32) returns (c: Counter)
  requires 0 <= start <= 1000
  ensures Valid(c) && value(c) == start
{
  c := Counter(start);
}

method bump(c: Counter) returns (c': Counter)
  requires Valid(c) && value(c) < 1000
  ensures Valid(c') && value(c') == value(c) + 1
{
  c' := Counter(c.n + 1);
}

method bumped_twice(start: int32) returns (result: int32)
  requires 0 <= start <= 998
  ensures result == start + 2
{
  var c := MakeCounter(start);
  c := bump(c);
  c := bump(c);
  result := value(c);
}

datatype State = State(open_handles: int32)

method acquire(s: State) returns (s': State, result: int32)
  requires 0 <= s.open_handles < 1000
  ensures s'.open_handles == s.open_handles + 1 && result == s.open_handles
{
  s' := State(s.open_handles + 1);
  result := s.open_handles;
}

method release(s: State, handle: int32) returns (s': State)
  requires s.open_handles > 0
  ensures s'.open_handles == s.open_handles - 1
{
  s' := State(s.open_handles - 1);
}

datatype Guard = Guard(handle: int32)

method MakeGuard(s: State) returns (s': State, g: Guard)
  requires 0 <= s.open_handles < 1000
  ensures s'.open_handles == s.open_handles + 1 && g.handle == s.open_handles
{
  var h: int32;
  s', h := acquire(s);
  g := Guard(h);
}

method Destroy(s: State, g: Guard) returns (s': State)
  requires s.open_handles > 0
  ensures s'.open_handles == s.open_handles - 1
{
  s' := release(s, g.handle);
}

method use_one(s: State) returns (s': State, result: int32)
  requires 0 <= s.open_handles < 1000
  ensures s'.open_handles == s.open_handles && result == s.open_handles
{
  var g: Guard;
  s', g := MakeGuard(s);
  result := g.handle;
  s' := Destroy(s', g);
}
