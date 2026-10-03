// Model B: a move copies the reference and sets the source to null. A read of the source is then a null dereference,
// and Dafny refuses it. Put `p.v` in place of `q.v` below and the proof fails with "target object may be null".
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method take(p0: Cell?) returns (result: int32)
  requires p0 != null
  requires -0x4000_0000 <= p0.v < 0x4000_0000
  ensures result as int == 2 * (old(p0.v) as int)
{
  var p := p0;
  var q := p;
  p := null;
  result := q.v + q.v;
}

// The model proves 14, and so does the fixed C++.
method Demo() {
  var c := new Cell;
  c.v := 7;
  var r := take(c);
  assert r == 14;
}
