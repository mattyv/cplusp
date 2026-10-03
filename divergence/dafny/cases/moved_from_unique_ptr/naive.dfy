// Model A: a unique_ptr is a nullable reference, and `std::move` copies it, so p and q are both the object.
// The model reads p after the move and gets the object. C++ leaves p null, and `*p` is undefined.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method take(p: Cell?) returns (result: int32)
  requires p != null
  requires -0x4000_0000 <= p.v < 0x4000_0000
  ensures result as int == 2 * (p.v as int)
{
  var q := p;
  result := p.v + q.v;
}

// The model proves 14. In C++ the read of p is a null dereference.
method Demo() {
  var c := new Cell;
  c.v := 7;
  var r := take(c);
  assert r == 14;
}
