// Model A: the pointer is a nullable reference to a cell, and `*p` is `p.v`.
// Dafny refuses the read, because p may be null. The model is stricter than the C++, which checks nothing.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method read(p: Cell?) returns (result: int32)
  ensures result == p.v
{
  result := p.v;
}
