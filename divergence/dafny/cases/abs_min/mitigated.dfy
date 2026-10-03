// Model B: the contract excludes the one value whose absolute value does not fit.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method magnitude(x: int32) returns (result: int32)
  requires x != -0x8000_0000
  ensures result as int == (if x < 0 then -(x as int) else x as int)
{
  result := if x < 0 then -x else x;
}
