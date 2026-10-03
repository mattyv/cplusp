// Model B: the contract excludes the one value that does not fit. It is the same contract as for `x + 1`.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method next(x: int32) returns (result: int32)
  requires x < 0x7FFF_FFFF
  ensures result as int == (x as int) + 1
{
  var y := x;
  y := y + 1;
  result := y;
}
