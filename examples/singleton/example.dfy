// The singleton is the State value of decision 0029: one value, with the static data member as its field, and every function that
// touches it takes it in and gives it back. A static member function that only reads is a function over the State. There is no
// object to model and no instance function, since the class has only static members. The invariant is a predicate over the State.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype State = State(count_: int32)

predicate Valid(s: State) { 0 <= s.count_ <= 1000 }

function count(s: State): int32
  requires Valid(s)
{
  s.count_
}

method bump(s: State) returns (s': State)
  requires Valid(s) && count(s) < 1000
  ensures Valid(s') && count(s') == count(s) + 1
{
  s' := State(s.count_ + 1);
}

method reset(s: State) returns (s': State)
  ensures Valid(s') && count(s') == 0
{
  s' := State(0);
}

method three_bumps(s: State) returns (s': State, result: int32)
  requires Valid(s) && count(s) <= 997
  ensures Valid(s') && count(s') == count(s) + 3 && result == count(s')
{
  s' := bump(s);
  s' := bump(s');
  s' := bump(s');
  result := count(s');
}

method reset_then_three(s: State) returns (s': State, result: int32)
  ensures result == 3
{
  s' := reset(s);
  s', result := three_bumps(s');
}
