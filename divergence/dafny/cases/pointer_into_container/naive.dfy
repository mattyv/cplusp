// Model A: a pointer is a nullable reference to a cell, and the vector is a seq. The two cannot alias.
// `&v[0]` is a new cell that holds a copy of the element, so `v := v + [1]` cannot change it, and the proof holds.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method read_after_grow(v0: seq<int32>, p: Cell?) returns (result: int32, v: seq<int32>)
  requires p != null
  ensures result == old(p.v)
{
  v := v0 + [1];
  result := p.v;
}

method first_then_grow(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires |v0| > 0
  ensures result == v0[0]
{
  var p := new Cell;
  p.v := v0[0];
  result, v := read_after_grow(v0, p);
}
