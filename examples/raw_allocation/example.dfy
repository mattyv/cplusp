// The trusted function is a method with no body, an axiom that states its contract. A unique_ptr is a nullable reference to a
// Cell, and the contract says the box is not null and holds x. The caller proves its result from that.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Cell {
  var v: int32
}

method {:axiom} make_box(x: int32) returns (result: Cell?)
  ensures result != null && result.v == x

method doubled(x: int32) returns (result: int32)
  requires -0x4000_0000 <= x < 0x4000_0000
  ensures result as int == 2 * (x as int)
{
  var b := make_box(x);
  result := b.v + b.v;
}
