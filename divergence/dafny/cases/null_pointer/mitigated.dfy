// Model B: the contract says the pointer is not null, in the C++ as `requires p != nullptr` and here as `requires p != null`.
// The caller carries the obligation.
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
