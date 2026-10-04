// A unique_ptr<int32_t> is a nullable reference to a Cell. make_unique allocates a new Cell, and the box is the only owner.
// A read needs `p != null`, in the C++ as `requires p != nullptr`, and the caller carries it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method boxed(x: int32) returns (result: Cell?)
  ensures result != null && result.v == x
{
  var c := new Cell;
  c.v := x;
  result := c;
}

method unboxed(p: Cell?) returns (result: int32)
  requires p != null
  ensures result == p.v
{
  result := p.v;
}

method round_trip(x: int32) returns (result: int32)
  ensures result == x
{
  var p := boxed(x);
  result := unboxed(p);
}
