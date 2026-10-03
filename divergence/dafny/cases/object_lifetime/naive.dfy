// Model A: the pointer is a nullable reference to a cell, and the cell is a Dafny object.
// A Dafny object never dies, so the pointer is valid for ever and the read is always allowed.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

class Holder {
  var p: Cell?
}

method read_later() returns (result: int32)
  ensures result == 42
{
  var h := new Holder;
  h.p := null;
  var local := new Cell;
  local.v := 42;
  h.p := local;
  result := h.p.v;
}
