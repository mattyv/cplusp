// Model B: the C++ copies the element out, so `&first` points at a local that no push_back moves, and this model is exact.
// The same text as model A is right for `&first` and wrong for `&v[0]`.
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
  var first := new Cell;
  first.v := v0[0];
  result, v := read_after_grow(v0, first);
}
