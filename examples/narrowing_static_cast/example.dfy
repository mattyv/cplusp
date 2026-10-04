// A cast to int8 needs a proof that the value fits. The model never wraps, so the proof comes from the contract.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int8 = x: int | -0x80 <= x < 0x80

method to_byte(x: int32) returns (result: int8)
  requires -0x80 <= x < 0x80
  ensures result as int == x as int
{
  result := x as int8;
}
