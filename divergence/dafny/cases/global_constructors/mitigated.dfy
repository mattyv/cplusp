// Model B: no global has a dynamic initializer. `derived_value` computes the value from `base_value` when it is called.
// `base_value` is a global of another file, so it is a field of the state object, and the contract says `reads` it.
// The order in which the files initialize does not enter the model, because fixed.cpp does not depend on it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class State {
  var base_value: int32
}

function derived_value(s: State): int32
  reads s
  requires s.base_value < 0x7FFF_FFFF
{ s.base_value + 1 }

method read_derived(s: State) returns (result: int32)
  requires s.base_value < 0x7FFF_FFFF
  ensures result == s.base_value + 1
{
  result := derived_value(s);
}
