// Model B: the contract says the variant holds an int32. The caller carries the obligation.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Alt = AnInt(i: int32) | ABool(b: bool)

method as_int(v: Alt) returns (result: int32)
  requires v.AnInt?
  ensures result == v.i
{
  result := v.i;
}
