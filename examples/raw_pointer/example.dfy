// A pointer parameter is a nullable reference. Dafny asks for `p != null` at every read, and the contract carries it, in the
// C++ as `requires p != nullptr`. The test in read_or gives the proof for the read in its second branch.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method read(p: Cell?) returns (result: int32)
  requires p != null
  ensures result == p.v
{
  result := p.v;
}

method read_or(p: Cell?, fallback: int32) returns (result: int32)
  ensures result == (if p == null then fallback else p.v)
{
  if p == null {
    return fallback;
  }
  return p.v;
}
