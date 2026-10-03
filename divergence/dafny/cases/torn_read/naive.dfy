// Model A: the getter is a function of the state, so two reads of it are equal and `difference` proves 0.
// In the C++, another thread may write `shared` between the two reads, and `difference()` may not be 0.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class State {
  var shared: int32
}

function read_shared(s: State): int32
  reads s
{
  s.shared
}

method difference(s: State) returns (result: int32)
  ensures result == 0
{
  result := read_shared(s) - read_shared(s);
}
