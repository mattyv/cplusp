// A pointer parameter is an Option value, decision 0029. Dafny asks for `p.Some?` at every read, and the contract carries it, in the
// C++ as `requires p != nullptr`. The test in read_or gives the proof for the read in its second branch.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method read(p: Option<int32>) returns (result: int32)
  requires p.Some?
  ensures result == p.value
{
  result := p.value;
}

method read_or(p: Option<int32>, fallback: int32) returns (result: int32)
  ensures result == (if !p.Some? then fallback else p.value)
{
  if !p.Some? {
    return fallback;
  }
  return p.value;
}
