// Model B: the contract excludes the one value that does not fit. The caller carries the obligation.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method neg(x: int32) returns (result: int32)
  requires x != -0x8000_0000
  ensures result as int == -(x as int)
{
  result := -x;
}
